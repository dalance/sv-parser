use crate::ast::*;
use crate::parser::*;

pub trait Node<'a> {
    fn test(&'a self) -> String;
    fn next(&'a self) -> Vec<AnyNode<'a>>;
}

impl<'a> Node<'a> for Span<'a> {
    fn test(&'a self) -> String {
        String::from("")
    }
    fn next(&'a self) -> Vec<AnyNode<'a>> {
        vec![]
    }
}
