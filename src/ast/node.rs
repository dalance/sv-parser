use crate::ast::*;
use crate::parser::*;

pub trait Node<'a> {
    fn next(&'a self) -> AnyNodes<'a>;
}

impl<'a> Node<'a> for Locate {
    fn next(&'a self) -> AnyNodes<'a> {
        vec![].into()
    }
}
