#![recursion_limit = "128"]

extern crate proc_macro;

use crate::proc_macro::TokenStream;
use quote::quote;
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
        impl<'a> Node<'a> for #name<'a> {
            fn next(&'a self) -> AnyNodes<'a> {
                #next
            }
        }

        impl<'a> From<&'a #name<'a>> for AnyNodes<'a>  {
            fn from(x: &'a #name<'a>) -> Self {
                vec![AnyNode::#name(x)].into()
            }
        }

        impl<'a> IntoIterator for &'a #name<'a> {
            type Item = AnyNode<'a>;
            type IntoIter = Iter<'a>;

            fn into_iter(self) -> Self::IntoIter {
                let nodes: AnyNodes<'a> = self.into();
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
    let (maybe_recursive,) = impl_parser_attribute(attr);

    let ident = &item.ident;
    let mut item = item.clone();

    let tracer = quote! {
        if cfg!(feature = "trace") {
            println!("{:<64} : {:<4},{:>032x} : {}", stringify!(#ident), s.offset, s.extra[0], s.fragment);
        }
    };
    let tracer: TokenStream = tracer.into();
    let tracer = parse_macro_input!(tracer as Stmt);

    let checker = quote! {
        if thread_context::PARSER_INDEX.with(|p| {
            if let Some(i) = p.borrow_mut().get(stringify!(#ident)) {
                return check_bit(s, i);
            } else {
                return false
            }
        }) {
            if cfg!(feature = "trace") {
                println!("{:<64} : loop detect", stringify!(#ident));
            }
            return Err(nom::Err::Error(nom::error::make_error(s, nom::error::ErrorKind::Fix)));
        }
    };
    let checker: TokenStream = checker.into();
    let checker = parse_macro_input!(checker as Stmt);

    let before = quote! {
        let s = thread_context::PARSER_INDEX.with(|p| {
            if let Some(i) = p.borrow_mut().get(stringify!(#ident)) {
                set_bit(s, i, true)
            } else {
                if cfg!(feature = "trace") {
                    println!("{:<64} : allocate failed", stringify!(#ident));
                }
                s
            }
        });
    };
    let before: TokenStream = before.into();
    let before = parse_macro_input!(before as Stmt);

    let mut body = quote! {};
    for s in &item.block.stmts {
        body = quote! {
            #body
            #s
        };
    }
    let body = quote! {
        let (s, ret) = { #body }?;
    };
    let body: TokenStream = body.into();
    let body = parse_macro_input!(body as Stmt);

    let after = quote! {
        Ok((clear_bit(s), ret))
    };
    let after: TokenStream = after.into();
    let after = parse_macro_input!(after as Expr);
    let after = Stmt::Expr(after);

    item.block.stmts.clear();
    item.block.stmts.push(tracer);
    if maybe_recursive {
        item.block.stmts.push(checker);
        item.block.stmts.push(before);
    }
    item.block.stmts.push(body);
    item.block.stmts.push(after);

    let gen = quote! {
        #item
    };
    gen.into()
}

fn impl_parser_attribute(attr: &AttributeArgs) -> (bool,) {
    let mut maybe_recursive = false;

    for a in attr {
        match a {
            NestedMeta::Meta(Meta::Word(x)) if x == "MaybeRecursive" => maybe_recursive = true,
            _ => panic!(),
        }
    }

    (maybe_recursive,)
}
