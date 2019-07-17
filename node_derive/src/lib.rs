#![recursion_limit = "128"]

extern crate proc_macro;

use crate::proc_macro::TokenStream;
use quote::quote;
use syn::{self, parse_macro_input, ItemFn};

#[proc_macro_derive(Node)]
pub fn node_derive(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).unwrap();
    impl_node(&ast)
}

fn impl_node(ast: &syn::DeriveInput) -> TokenStream {
    let name = &ast.ident;

    let next = match ast.data {
        syn::Data::Enum(ref data) => {
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
        syn::Data::Struct(_) => {
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
            fn test(&'a self) -> String {
                format!("{}", stringify!(#name))
            }

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

fn impl_any_node(ast: &syn::DeriveInput) -> TokenStream {
    let ref data = match ast.data {
        syn::Data::Enum(ref data) => data,
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
pub fn trace(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let item = parse_macro_input!(item as ItemFn);
    impl_trace(&item)
}

fn impl_trace(item: &syn::ItemFn) -> TokenStream {
    let ident = &item.ident;
    let mut item = item.clone();

    let tracer = quote! {
        if cfg!(feature = "trace") {
            println!("{:<48} : {:<4},{:>032x} : {}", stringify!(#ident), s.offset, s.extra, s.fragment);
        }
    };
    let tracer: TokenStream = tracer.into();
    let tracer = parse_macro_input!(tracer as syn::Stmt);

    let checker = quote! {
        if thread_context::TABLE.with(|t| {
            if let Some(i) = t.borrow_mut().get_or_allocate(stringify!(#ident)) {
                return check_bit(s, i);
            } else {
                return false
            }
        }) {
            if cfg!(feature = "trace") {
                println!("{:<48} : loop detect", stringify!(#ident));
            }
            return Err(nom::Err::Error(nom::error::make_error(s, nom::error::ErrorKind::Fix)));
        }
    };
    let checker: TokenStream = checker.into();
    let checker = parse_macro_input!(checker as syn::Stmt);

    let before = quote! {
        let s = thread_context::TABLE.with(|t| {
            if let Some(i) = t.borrow_mut().get_or_allocate(stringify!(#ident)) {
                //println!("{}:{} set", stringify!(#ident), i);
                set_bit(s, i, true)
            } else {
                if cfg!(feature = "trace") {
                    println!("{:<48} : allocate failed", stringify!(#ident));
                }
                s
            }
        });
    };
    let before: TokenStream = before.into();
    let before = parse_macro_input!(before as syn::Stmt);

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
    let body = parse_macro_input!(body as syn::Stmt);

    let after = quote! {
        Ok((clear_bit(s), ret))
    };
    let after: TokenStream = after.into();
    let after = parse_macro_input!(after as syn::Expr);
    let after = syn::Stmt::Expr(after);

    item.block.stmts.clear();
    item.block.stmts.push(tracer);
    item.block.stmts.push(checker);
    item.block.stmts.push(before);
    item.block.stmts.push(body);
    item.block.stmts.push(after);

    let gen = quote! {
        #item
    };
    gen.into()
}

#[proc_macro_attribute]
pub fn rec(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let item = parse_macro_input!(item as ItemFn);
    impl_rec(&item)
}

fn impl_rec(item: &syn::ItemFn) -> TokenStream {
    let ident = &item.ident;
    let mut item = item.clone();
    let tracer = quote! {
        if thread_context::MAP_MUT.with(|m| {
            if let Some(x) = m.borrow().get(stringify!(#ident)) {
                if *x == s.offset {
                    return true;
                }
            }
            m.borrow_mut().insert(stringify!(#ident), s.offset);
            false
        }) {
            return Err(nom::Err::Error(nom::error::make_error(s, nom::error::ErrorKind::Fix)));
        }
    };
    let tracer: TokenStream = tracer.into();
    let tracer = parse_macro_input!(tracer as syn::Stmt);
    item.block.stmts.insert(0, tracer);

    let gen = quote! {
        #item
    };
    gen.into()
}
