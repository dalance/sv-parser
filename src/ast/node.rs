use crate::ast::*;
use crate::parser::*;

pub trait Node<'a> {
    fn test(&'a self) -> String;
    fn next(&'a self) -> AnyNodes<'a>;
}

impl<'a> Node<'a> for Span<'a> {
    fn test(&'a self) -> String {
        String::from("")
    }
    fn next(&'a self) -> AnyNodes<'a> {
        vec![].into()
    }
}
