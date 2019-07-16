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
        println!("{}: {:?}", stringify!(#ident), s);
    };
    let tracer: TokenStream = tracer.into();
    let tracer = parse_macro_input!(tracer as syn::Stmt);
    item.block.stmts.insert(0, tracer);

    let gen = quote! {
        #item
    };
    gen.into()
}
