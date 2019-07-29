#![recursion_limit = "128"]

extern crate proc_macro;

use crate::proc_macro::TokenStream;
use quote::quote;
use syn::Data::{Enum, Struct};
use syn::{self, DeriveInput};

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
            fn next(&'a self) -> RefNodes<'a> {
                #next
            }
        }

        impl<'a> From<&'a #name> for RefNodes<'a>  {
            fn from(x: &'a #name) -> Self {
                vec![RefNode::#name(x)].into()
            }
        }

        impl From<#name> for AnyNode  {
            fn from(x: #name) -> Self {
                AnyNode::#name(x)
            }
        }

        impl<'a> IntoIterator for &'a #name {
            type Item = RefNode<'a>;
            type IntoIter = Iter<'a>;

            fn into_iter(self) -> Self::IntoIter {
                let nodes: RefNodes = self.into();
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
            impl TryFrom<AnyNode> for #ident  {
                type Error = ();
                fn try_from(x: AnyNode) -> Result<Self, Self::Error> {
                    match x {
                        AnyNode::#ident(x) => Ok(x),
                        _ => Err(()),
                    }
                }
            }
        };
        items = quote! {
            #items
            #item
        };
    }

    let gen = quote! {
        #items
    };
    gen.into()
}

#[proc_macro_derive(RefNode)]
pub fn ref_node_derive(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).unwrap();
    impl_ref_node(&ast)
}

fn impl_ref_node(ast: &DeriveInput) -> TokenStream {
    let ref data = match ast.data {
        Enum(ref data) => data,
        _ => unreachable!(),
    };

    let mut items = quote! {};
    for v in &data.variants {
        let ident = &v.ident;
        let item = quote! {
            RefNode::#ident(x) => x.next(),
        };
        items = quote! {
            #items
            #item
        };
    }

    let name = &ast.ident;
    let gen = quote! {
        impl<'a> #name<'a> {
            fn next(&self) -> RefNodes<'a> {
                match self {
                    #items
                }
            }
        }
    };
    gen.into()
}
