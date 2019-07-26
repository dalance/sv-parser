#![recursion_limit = "128"]

extern crate proc_macro;

use crate::proc_macro::TokenStream;
use quote::quote;
use std::str::FromStr;
use syn::Data::{Enum, Struct};
use syn::{self, parse_macro_input, AttributeArgs, DeriveInput, ItemFn, Meta, NestedMeta, Stmt};

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

#[proc_macro_attribute]
pub fn parser(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr = parse_macro_input!(attr as AttributeArgs);
    let item = parse_macro_input!(item as ItemFn);
    impl_parser(&attr, &item)
}

fn impl_parser(attr: &AttributeArgs, item: &ItemFn) -> TokenStream {
    let ambiguous = impl_parser_attribute(attr);

    let trace = impl_parser_trace(&item);
    let trace = parse_macro_input!(trace as Stmt);

    let body = if ambiguous {
        impl_parser_body_ambiguous(&item)
    } else {
        impl_parser_body(&item)
    };
    let body = parse_macro_input!(body as Stmt);

    let mut item = item.clone();

    item.block.stmts.clear();
    item.block.stmts.push(trace);
    item.block.stmts.push(body);

    let gen = quote! {
        #item
    };
    gen.into()
}

fn impl_parser_attribute(attr: &AttributeArgs) -> bool {
    let mut ambiguous = false;

    for a in attr {
        match a {
            NestedMeta::Meta(Meta::Word(x)) if x == "Ambiguous" => ambiguous = true,
            _ => panic!(),
        }
    }

    ambiguous
}

fn impl_parser_trace(item: &ItemFn) -> TokenStream {
    let ident = &item.ident;

    let gen = quote! {
        #[cfg(feature = "trace")]
        let s = trace(s, stringify!(#ident));
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
        {
            #gen
        }
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
        {
            #gen
        }
    };

    gen.into()
}
