#![recursion_limit = "128"]

extern crate proc_macro;

use crate::proc_macro::TokenStream;
use quote::quote;
use syn;

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
                    #name::#ident(x) => { let ret: AnyNode<'a> = x.into(); vec![ret] },
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
        _ => {
            quote! {
                vec![]
            }
        }
    };

    let gen = quote! {
        impl<'a> Node<'a> for #name<'a> {
            fn test(&'a self) -> String {
                format!("{}", stringify!(#name))
            }

            fn next(&'a self) -> Vec<AnyNode<'a>> {
                #next
            }
        }

        impl<'a> From<&'a #name<'a>> for AnyNode<'a>  {
            fn from(x: &'a #name<'a>) -> Self {
                AnyNode::#name(x)
            }
        }

        impl<'a> IntoIterator for &'a #name<'a> {
            type Item = AnyNode<'a>;
            type IntoIter = Iter<'a>;

            fn into_iter(self) -> Self::IntoIter {
                let node: AnyNode<'a> = self.into();
                Iter { next: vec![node] }
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
            fn next(&self) -> Vec<AnyNode<'a>> {
                match self {
                    #items
                }
            }
        }
    };
    gen.into()
}
