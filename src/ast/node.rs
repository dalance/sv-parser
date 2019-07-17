use crate::ast::*;
use crate::parser::*;

pub trait Node<'a> {
    fn next(&'a self) -> AnyNodes<'a>;
}

impl<'a> Node<'a> for Span<'a> {
    fn next(&'a self) -> AnyNodes<'a> {
        vec![].into()
    }
}
