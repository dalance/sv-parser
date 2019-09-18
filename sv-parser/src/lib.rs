#![recursion_limit = "256"]

use nom::combinator::all_consuming;
use std::collections::HashMap;
use std::fmt;
use std::path::Path;
use sv_parser_error::{Error, ErrorKind};
use sv_parser_parser::{lib_parser, sv_parser, Span, SpanInfo};
use sv_parser_pp::preprocess::{preprocess, Define, Defines, PreprocessedText};
pub use sv_parser_syntaxtree::*;

pub struct SyntaxTree {
    node: AnyNode,
    text: PreprocessedText,
}

impl SyntaxTree {
    pub fn get_str(&self, locate: &Locate) -> &str {
        unsafe {
            self.text
                .text()
                .get_unchecked(locate.offset..locate.offset + locate.len)
        }
    }
}

impl fmt::Display for SyntaxTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::from("");
        let mut skip = false;
        let mut depth = 0;
        for node in self.into_iter().event() {
            match node {
                NodeEvent::Enter(RefNode::Locate(locate)) if !skip => {
                    ret.push_str(&format!("{}{}\n", " ".repeat(depth), self.get_str(locate)));
                    depth += 1;
                }
                NodeEvent::Enter(RefNode::WhiteSpace(_)) => {
                    skip = true;
                }
                NodeEvent::Leave(RefNode::WhiteSpace(_)) => {
                    skip = false;
                }
                NodeEvent::Enter(_) => {
                    depth += 1;
                }
                NodeEvent::Leave(_) => {
                    depth -= 1;
                }
            }
        }
        write!(f, "{}", ret)
    }
}

impl<'a> IntoIterator for &'a SyntaxTree {
    type Item = RefNode<'a>;
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        let ref_node: RefNode = (&self.node).into();
        ref_node.into_iter()
    }
}

pub fn parse_sv<T: AsRef<Path>, U: AsRef<Path>>(
    path: T,
    pre_defines: &HashMap<String, Option<Define>>,
    include_paths: &[U],
) -> Result<(SyntaxTree, Defines), Error> {
    let (text, defines) = preprocess(path, pre_defines, include_paths)?;
    let span = Span::new_extra(text.text(), SpanInfo::default());
    let result = all_consuming(sv_parser)(span);
    match result {
        Ok((_, x)) => Ok((
            SyntaxTree {
                node: x.into(),
                text,
            },
            defines,
        )),
        Err(_) => Err(ErrorKind::Parse.into()),
    }
}

pub fn parse_lib<T: AsRef<Path>, U: AsRef<Path>>(
    path: T,
    pre_defines: &HashMap<String, Option<Define>>,
    include_paths: &[U],
) -> Result<(SyntaxTree, Defines), Error> {
    let (text, defines) = preprocess(path, pre_defines, include_paths)?;
    let span = Span::new_extra(text.text(), SpanInfo::default());
    let result = all_consuming(lib_parser)(span);
    match result {
        Ok((_, x)) => Ok((
            SyntaxTree {
                node: x.into(),
                text,
            },
            defines,
        )),
        Err(_) => Err(ErrorKind::Parse.into()),
    }
}
