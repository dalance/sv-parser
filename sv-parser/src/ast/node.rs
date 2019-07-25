use crate::ast::*;

pub(crate) trait Node<'a> {
    fn next(&'a self) -> RefNodes<'a>;
}

impl<'a> Node<'a> for Locate {
    fn next(&'a self) -> RefNodes<'a> {
        vec![].into()
    }
}
