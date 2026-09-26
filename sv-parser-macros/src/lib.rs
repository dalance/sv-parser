//! Procedural macros for generating CST navigation and conversion code in `sv-parser`.
//!
//! Provides custom derive macros:
//! - `#[derive(Node)]`: Implements `Node`, conversions to `RefNodes`, `RefNode`, `AnyNode`,
//!   `TryFrom` for `Locate`, and `IntoIterator`.
//! - `#[derive(AnyNode)]`: Implements downcasting `TryFrom<AnyNode>` for each syntax node variant,
//!   and reference conversion `From<&AnyNode> for RefNode`.
//! - `#[derive(RefNode)]`: Implements `next()` and `IntoIterator` on the umbrella `RefNode` enum.

#![recursion_limit = "128"]

extern crate proc_macro;

use crate::proc_macro::TokenStream;
use quote::quote;
use syn::Data::{Enum, Struct};
use syn::{self, DeriveInput};

/// Derives the `Node` trait, conversion traits (`From`, `Into`), and `IntoIterator` for a CST node.
///
/// For structs, child nodes are extracted from `self.nodes`.
/// For enums, calls are delegated to the active variant.
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

        impl<'a> From<&'a #name> for RefNodes<'a> {
            fn from(x: &'a #name) -> Self {
                vec![RefNode::#name(x)].into()
            }
        }

        impl From<#name> for AnyNode {
            fn from(x: #name) -> Self {
                AnyNode::#name(x)
            }
        }

        impl<'a> From<&'a #name> for RefNode<'a> {
            fn from(x: &'a #name) -> Self {
                RefNode::#name(x)
            }
        }

        impl core::convert::TryFrom<#name> for Locate {
            type Error = ();
            fn try_from(x: #name) -> Result<Self, Self::Error> {
                Self::try_from(&x)
            }
        }

        impl<'a> core::convert::TryFrom<&'a #name> for Locate {
            type Error = ();
            fn try_from(x: &'a #name) -> Result<Self, Self::Error> {
                let mut locate: Option<Locate> = None;
                for x in x {
                    match x {
                        RefNode::Locate(x) => if let Some(loc) = locate {
                            assert_eq!(x.offset, loc.offset + loc.len);
                            locate = Some(Locate { offset: loc.offset, line: loc.line, len: loc.len + x.len });
                        } else {
                            locate = Some(*x);
                        },
                        _ => (),
                    }
                }
                locate.ok_or(())
            }
        }

        impl<'a> IntoIterator for &'a #name {
            type Item = RefNode<'a>;
            type IntoIter = Iter<'a>;

            fn into_iter(self) -> Self::IntoIter {
                let mut nodes: RefNodes = self.into();
                nodes.0.reverse();
                Iter { next: nodes }
            }
        }
    };
    gen.into()
}

/// Derives downcasting `TryFrom<AnyNode>` and conversion to `RefNode` for the `AnyNode` umbrella enum.
#[proc_macro_derive(AnyNode)]
pub fn any_node_derive(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).unwrap();
    impl_any_node(&ast)
}

fn impl_any_node(ast: &DeriveInput) -> TokenStream {
    let data = &match ast.data {
        Enum(ref data) => data,
        _ => unreachable!(),
    };

    let mut try_froms = quote! {};
    let mut from_items = quote! {};
    for v in &data.variants {
        let ident = &v.ident;

        try_froms = quote! {
            #try_froms
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

        from_items = quote! {
            #from_items
            AnyNode::#ident(x) => RefNode::#ident(&x),
        };
    }

    let gen = quote! {
        #try_froms

        impl<'a> From<&'a AnyNode> for RefNode<'a>  {
            fn from(x: &'a AnyNode) -> Self {
                match x {
                    #from_items
                }
            }
        }
    };
    gen.into()
}

/// Derives `next()` child navigation and `IntoIterator` for the `RefNode` umbrella enum.
#[proc_macro_derive(RefNode)]
pub fn ref_node_derive(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).unwrap();
    impl_ref_node(&ast)
}

fn impl_ref_node(ast: &DeriveInput) -> TokenStream {
    let data = &match ast.data {
        Enum(ref data) => data,
        _ => unreachable!(),
    };

    let mut next_items = quote! {};
    let mut into_iter_items = quote! {};
    for v in &data.variants {
        let ident = &v.ident;
        next_items = quote! {
            #next_items
            RefNode::#ident(x) => x.next(),
        };
        into_iter_items = quote! {
            #into_iter_items
            RefNode::#ident(x) => x.into_iter(),
        };
    }

    let name = &ast.ident;
    let gen = quote! {
        impl<'a> #name<'a> {
            fn next(&self) -> RefNodes<'a> {
                match self {
                    #next_items
                }
            }
        }

        impl<'a> IntoIterator for #name<'a> {
            type Item = RefNode<'a>;
            type IntoIter = Iter<'a>;

            fn into_iter(self) -> Self::IntoIter {
                match self {
                    #into_iter_items
                }
            }
        }
    };
    gen.into()
}
