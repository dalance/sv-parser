#![recursion_limit = "128"]

extern crate proc_macro;

use crate::proc_macro::TokenStream;
use quote::quote;
use std::str::FromStr;
use syn::Data::{Enum, Struct};
use syn::{
    self, parse_macro_input, AttributeArgs, DeriveInput, Expr, ItemFn, Meta, NestedMeta, Stmt,
};

#[proc_macro_derive(Node)]
pub fn node_derive(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).unwrap();
    impl_node(&ast)
}

fn impl_node(ast: &DeriveInput) -> TokenStream {
    let name = &ast.ident;

    let next = match ast.data {
        Enum(ref data) => {
            let mut items = quote! {};
            for v in &data.variants {
                let ident = &v.ident;
                let item = quote! {
                    #name::#ident(x) => { x.into() },
                };
                items = quote! {
                    #items
                    #item
                };
            }

            quote! {
                match self {
                    #items
                }
            }
        }
        Struct(_) => {
            quote! {
                (&(self.nodes)).into()
            }
        }
        _ => {
            quote! {
                vec![].into()
            }
        }
    };

    let gen = quote! {
        impl<'a> Node<'a> for #name {
            fn next(&'a self) -> AnyNodes<'a> {
                #next
            }
        }

        impl<'a> From<&'a #name> for AnyNodes<'a>  {
            fn from(x: &'a #name) -> Self {
                vec![AnyNode::#name(x)].into()
            }
        }

        impl<'a> IntoIterator for &'a #name {
            type Item = AnyNode<'a>;
            type IntoIter = Iter<'a>;

            fn into_iter(self) -> Self::IntoIter {
                let nodes: AnyNodes = self.into();
                Iter { next: nodes }
            }
        }
    };
    gen.into()
}

#[proc_macro_derive(AnyNode)]
pub fn any_node_derive(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).unwrap();
    impl_any_node(&ast)
}

fn impl_any_node(ast: &DeriveInput) -> TokenStream {
    let ref data = match ast.data {
        Enum(ref data) => data,
        _ => unreachable!(),
    };

    let mut items = quote! {};
    for v in &data.variants {
        let ident = &v.ident;
        let item = quote! {
            AnyNode::#ident(x) => x.next(),
        };
        items = quote! {
            #items
            #item
        };
    }

    let name = &ast.ident;
    let gen = quote! {
        impl<'a> #name<'a> {
            fn next(&self) -> AnyNodes<'a> {
                match self {
                    #items
                }
            }
        }
    };
    gen.into()
}

#[proc_macro_attribute]
pub fn parser(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr = parse_macro_input!(attr as AttributeArgs);
    let item = parse_macro_input!(item as ItemFn);
    impl_parser(&attr, &item)
}

fn impl_parser(attr: &AttributeArgs, item: &ItemFn) -> TokenStream {
    let (maybe_recursive, ambiguous, memoize) = impl_parser_attribute(attr);

    let trace = impl_parser_trace(&item);
    let trace = parse_macro_input!(trace as Stmt);

    let check_recursive_flag = impl_parser_check_recursive_flag(&item);
    let check_recursive_flag = parse_macro_input!(check_recursive_flag as Stmt);

    let set_recursive_flag = impl_parser_set_recursive_flag(&item);
    let set_recursive_flag = parse_macro_input!(set_recursive_flag as Stmt);

    let body = if ambiguous {
        impl_parser_body_ambiguous(&item)
    } else {
        impl_parser_body(&item)
    };
    let body = parse_macro_input!(body as Stmt);

    let body_unwrap = impl_parser_body_unwrap(&item);
    let body_unwrap = parse_macro_input!(body_unwrap as Stmt);

    let clear_recursive_flags = impl_parser_clear_recursive_flags(&item);
    let clear_recursive_flags = parse_macro_input!(clear_recursive_flags as Expr);
    let clear_recursive_flags = Stmt::Expr(clear_recursive_flags);

    let check_failed_memo = impl_parser_check_failed_memo(&item);
    let check_failed_memo = parse_macro_input!(check_failed_memo as Stmt);

    let set_failed_memo = impl_parser_set_failed_memo(&item);
    let set_failed_memo = parse_macro_input!(set_failed_memo as Stmt);

    let mut item = item.clone();

    item.block.stmts.clear();
    item.block.stmts.push(trace);
    if memoize {
        item.block.stmts.push(check_failed_memo);
    }
    if maybe_recursive {
        item.block.stmts.push(check_recursive_flag);
        item.block.stmts.push(set_recursive_flag);
    }
    item.block.stmts.push(body);
    if memoize {
        item.block.stmts.push(set_failed_memo);
    }
    item.block.stmts.push(body_unwrap);
    item.block.stmts.push(clear_recursive_flags);

    let gen = quote! {
        #item
    };
    gen.into()
}

fn impl_parser_attribute(attr: &AttributeArgs) -> (bool, bool, bool) {
    let mut maybe_recursive = false;
    let mut ambiguous = false;
    let mut memoize = false;

    for a in attr {
        match a {
            NestedMeta::Meta(Meta::Word(x)) if x == "MaybeRecursive" => maybe_recursive = true,
            NestedMeta::Meta(Meta::Word(x)) if x == "Ambiguous" => ambiguous = true,
            NestedMeta::Meta(Meta::Word(x)) if x == "Memoize" => memoize = true,
            _ => panic!(),
        }
    }

    (maybe_recursive, ambiguous, memoize)
}

fn impl_parser_trace(item: &ItemFn) -> TokenStream {
    let ident = &item.ident;

    let gen = quote! {
        #[cfg(feature = "trace")]
        let s = trace(s, stringify!(#ident));
    };
    gen.into()
}

fn impl_parser_check_recursive_flag(item: &ItemFn) -> TokenStream {
    let ident = &item.ident;

    let gen = quote! {
        if thread_context::PARSER_INDEX.with(|p| {
            if let Some(i) = p.borrow_mut().get(stringify!(#ident)) {
                return check_recursive_flag(s, i);
            } else {
                return false
            }
        }) {
            #[cfg(feature = "trace")]
            println!("{:<128} : loop detect", format!("{}{}", " ".repeat(s.extra.depth), stringify!(#ident)));
            return Err(nom::Err::Error(nom::error::make_error(s, nom::error::ErrorKind::Fix)));
        }
    };
    gen.into()
}

fn impl_parser_set_recursive_flag(item: &ItemFn) -> TokenStream {
    let ident = &item.ident;

    let gen = quote! {
        let s = thread_context::PARSER_INDEX.with(|p| {
            if let Some(i) = p.borrow_mut().get(stringify!(#ident)) {
                set_recursive_flag(s, i, true)
            } else {
                #[cfg(feature = "trace")]
                println!("{:<128} : allocate failed", format!("{}{}", " ".repeat(s.extra.depth), stringify!(#ident)));
                s
            }
        });
    };
    gen.into()
}

fn impl_parser_body(item: &ItemFn) -> TokenStream {
    let mut gen = quote! {};
    for s in &item.block.stmts {
        gen = quote! {
            #gen
            #s
        };
    }
    let gen = quote! {
        let body_ret = { #gen };
    };
    gen.into()
}

fn impl_parser_body_ambiguous(item: &ItemFn) -> TokenStream {
    let mut token = quote! {};
    for s in &item.block.stmts {
        token = quote! {
            #token
            #s
        };
    }
    let mut token = token.to_string();

    let ambiguous_cnt: Vec<&str> = token.matches("ambiguous").collect();
    let ambiguous_cnt = ambiguous_cnt.len();

    let mut replace_parsers = Vec::new();
    for i in 0..ambiguous_cnt {
        let pos = token.find("ambiguous").unwrap();
        let (head, rest) = token.split_at(pos);
        if rest.starts_with("ambiguous_opt") {
            let rest = rest.replacen("ambiguous_opt", &format!("amb_temporary{}", i), 1);
            token = format!("{}{}", head, rest);
            replace_parsers.push(("opt", "none"));
        } else if rest.starts_with("ambiguous_alt") {
            let rest = rest.replacen("ambiguous_alt", &format!("amb_temporary{}", i), 1);
            token = format!("{}{}", head, rest);
            replace_parsers.push(("alt_left", "alt_right"));
        }
    }

    let mut gen = quote! {};
    for i in 0..2_u32.pow(ambiguous_cnt as u32) {
        let mut token = token.clone();
        for j in 0..ambiguous_cnt {
            let (p0, p1) = replace_parsers[j];
            let repl = if ((i >> j) & 1) == 0 { p0 } else { p1 };
            token = token.replace(&format!("amb_temporary{}", j), repl);
        }
        let token = format!("{{ {} }}", token);
        let token = TokenStream::from_str(&token).unwrap();
        let token = parse_macro_input!(token as Stmt);
        gen = quote! {
            #gen
            |s| #token,
        };
    }

    let gen = quote! {
        alt((
            #gen
        ))(s)
    };

    let gen = quote! {
        let body_ret = { #gen };
    };

    gen.into()
}

fn impl_parser_body_unwrap(_item: &ItemFn) -> TokenStream {
    let gen = quote! {
        let (s, ret) = body_ret?;
    };
    gen.into()
}

fn impl_parser_clear_recursive_flags(_item: &ItemFn) -> TokenStream {
    let gen = quote! {
        Ok((clear_recursive_flags(s), ret))
    };
    gen.into()
}

fn impl_parser_check_failed_memo(item: &ItemFn) -> TokenStream {
    let ident = &item.ident;

    let gen = quote! {
        let offset = {
            //if thread_context::FAILED_MEMO.with(|m| { m.borrow().get(&(stringify!(#ident), s.offset)).is_some() }) {
            //    #[cfg(feature = "trace")]
            //    println!("{:<128} : memoized failure", format!("{}{}", " ".repeat(s.extra.depth), stringify!(#ident)));
            //    return Err(nom::Err::Error(nom::error::make_error(s, nom::error::ErrorKind::Fix)));
            //}
            if let Some(x) = thread_context::FAILED_MEMO.with(|m| { if let Some(x) = m.borrow().get(&(stringify!(#ident), s.offset)) { Some(*x) } else { None } }) {
                if x {
                    #[cfg(feature = "trace")]
                    println!("{:<128} : memoized failure", format!("{}{}", " ".repeat(s.extra.depth), stringify!(#ident)));
                    return Err(nom::Err::Error(nom::error::make_error(s, nom::error::ErrorKind::Fix)));
                } else {
                    #[cfg(feature = "trace")]
                    println!("{:<128} : memoized success", format!("{}{}", " ".repeat(s.extra.depth), stringify!(#ident)));
                }
            }
            s.offset
        };
    };
    gen.into()
}

fn impl_parser_set_failed_memo(item: &ItemFn) -> TokenStream {
    let ident = &item.ident;

    let gen = quote! {
        //if body_ret.is_err() {
        //    thread_context::FAILED_MEMO.with(|m| {
        //        m.borrow_mut().insert((stringify!(#ident), offset), ());
        //    })
        //}
        if body_ret.is_err() {
            thread_context::FAILED_MEMO.with(|m| {
                m.borrow_mut().insert((stringify!(#ident), offset), true);
            })
        } else {
            thread_context::FAILED_MEMO.with(|m| {
                m.borrow_mut().insert((stringify!(#ident), offset), false);
            })
        }
    };
    gen.into()
}
