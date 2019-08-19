#![recursion_limit = "256"]

use nom::combinator::all_consuming;
use sv_parser_parser::{lib_parser, sv_parser, Span, SpanInfo};
pub use sv_parser_syntaxtree::*;

pub struct SyntaxTree<'a> {
    node: AnyNode,
    buf: &'a str,
}

impl<'a> SyntaxTree<'a> {
    pub fn get_str(&self, locate: &Locate) -> &'a str {
        unsafe {
            self.buf
                .get_unchecked(locate.offset..locate.offset + locate.len)
        }
    }
}

impl<'a> IntoIterator for &'a SyntaxTree<'a> {
    type Item = RefNode<'a>;
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        let ref_node: RefNode = (&self.node).into();
        ref_node.into_iter()
    }
}

pub fn parse_sv(s: &str) -> Result<SyntaxTree, ()> {
    let span = Span::new_extra(s, SpanInfo::default());
    match all_consuming(sv_parser)(span) {
        Ok((_, x)) => Ok(SyntaxTree {
            node: AnyNode::SourceText(x),
            buf: s,
        }),
        Err(_) => Err(()),
    }
}

pub fn parse_lib(s: &str) -> Result<SyntaxTree, ()> {
    let span = Span::new_extra(s, SpanInfo::default());
    match all_consuming(lib_parser)(span) {
        Ok((_, x)) => Ok(SyntaxTree {
            node: AnyNode::LibraryText(x),
            buf: s,
        }),
        Err(_) => Err(()),
    }
}
