use crate::ast::*;
use crate::parser::*;

impl<'a> From<&'a Span<'a>> for AnyNode<'a> {
    fn from(x: &'a Span<'a>) -> Self {
        AnyNode::Span(x)
    }
}

include!(concat!(env!("OUT_DIR"), "/any_node.rs"));

pub struct Iter<'a> {
    pub next: Vec<AnyNode<'a>>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = AnyNode<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let ret = self.next.pop();
        if let Some(x) = ret.clone() {
            let mut x = x.next();
            x.reverse();
            self.next.append(&mut x);
        }
        ret
    }
}
