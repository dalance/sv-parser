#![recursion_limit = "256"]

use nom::combinator::all_consuming;
use nom_greedyerror::error_position;
use std::collections::HashMap;
use std::fmt;
use std::hash::BuildHasher;
use std::path::{Path, PathBuf};
pub use sv_parser_error::Error;
use sv_parser_parser::{lib_parser, sv_parser, Span, SpanInfo};
pub use sv_parser_pp::preprocess::{
    preprocess, preprocess_str, Define, DefineText, Defines, PreprocessedText,
};
pub use sv_parser_syntaxtree::*;

pub struct SyntaxTree {
    node: AnyNode,
    text: PreprocessedText,
}

impl SyntaxTree {
    pub fn get_str<'a, T: Into<RefNodes<'a>>>(&self, nodes: T) -> Option<&str> {
        let mut beg = None;
        let mut end = 0;
        for n in Iter::new(nodes.into()) {
            if let RefNode::Locate(x) = n {
                if beg.is_none() {
                    beg = Some(x.offset);
                }
                end = x.offset + x.len;
            }
        }
        if let Some(beg) = beg {
            let ret = unsafe { self.text.text().get_unchecked(beg..end) };
            Some(ret)
        } else {
            None
        }
    }

    pub fn get_origin(&self, locate: &Locate) -> Option<(&PathBuf, usize)> {
        self.text.origin(locate.offset)
    }
}

impl fmt::Display for SyntaxTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::from("");
        let mut skip = false;
        let mut depth = 0;
        for node in self.into_iter().event() {
            match node {
                NodeEvent::Enter(RefNode::Locate(locate)) => {
                    if !skip {
                        ret.push_str(&format!(
                            "{}Token: '{}' @ line:{}\n",
                            " ".repeat(depth),
                            self.get_str(locate).unwrap(),
                            locate.line,
                        ));
                    }
                    depth += 1;
                }
                NodeEvent::Enter(RefNode::WhiteSpace(_)) => {
                    skip = true;
                }
                NodeEvent::Leave(RefNode::WhiteSpace(_)) => {
                    skip = false;
                }
                NodeEvent::Enter(x) => {
                    if !skip {
                        ret.push_str(&format!("{}{}\n", " ".repeat(depth), x));
                    }
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

pub fn parse_sv<T: AsRef<Path>, U: AsRef<Path>, V: BuildHasher>(
    path: T,
    pre_defines: &HashMap<String, Option<Define>, V>,
    include_paths: &[U],
    ignore_include: bool,
) -> Result<(SyntaxTree, Defines), Error> {
    let (text, defines) = preprocess(path, pre_defines, include_paths, false, ignore_include)?;
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
        Err(x) => {
            let pos = match x {
                nom::Err::Incomplete(_) => None,
                nom::Err::Error(e) => error_position(&e),
                nom::Err::Failure(e) => error_position(&e),
            };
            let origin = if let Some(pos) = pos {
                if let Some(origin) = text.origin(pos) {
                    Some((origin.0.clone(), origin.1))
                } else {
                    None
                }
            } else {
                None
            };
            Err(Error::Parse(origin))
        }
    }
}

pub fn parse_sv_str<T: AsRef<Path>, U: AsRef<Path>, V: BuildHasher>(
    s: &str,
    path: T,
    pre_defines: &HashMap<String, Option<Define>, V>,
    include_paths: &[U],
    ignore_include: bool,
) -> Result<(SyntaxTree, Defines), Error> {
    let (text, defines) = preprocess_str(
        s,
        path,
        pre_defines,
        include_paths,
        ignore_include,
        false,
        0,
    )?;
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
        Err(x) => {
            let pos = match x {
                nom::Err::Incomplete(_) => None,
                nom::Err::Error(e) => error_position(&e),
                nom::Err::Failure(e) => error_position(&e),
            };
            let origin = if let Some(pos) = pos {
                if let Some(origin) = text.origin(pos) {
                    Some((origin.0.clone(), origin.1))
                } else {
                    None
                }
            } else {
                None
            };
            Err(Error::Parse(origin))
        }
    }
}

pub fn parse_lib<T: AsRef<Path>, U: AsRef<Path>, V: BuildHasher>(
    path: T,
    pre_defines: &HashMap<String, Option<Define>, V>,
    include_paths: &[U],
    strip_comments: bool,
    ignore_include: bool,
) -> Result<(SyntaxTree, Defines), Error> {
    let (text, defines) = preprocess(
        path,
        pre_defines,
        include_paths,
        strip_comments,
        ignore_include,
    )?;
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
        Err(x) => {
            let pos = match x {
                nom::Err::Incomplete(_) => None,
                nom::Err::Error(e) => error_position(&e),
                nom::Err::Failure(e) => error_position(&e),
            };
            let origin = if let Some(pos) = pos {
                if let Some(origin) = text.origin(pos) {
                    Some((origin.0.clone(), origin.1))
                } else {
                    None
                }
            } else {
                None
            };
            Err(Error::Parse(origin))
        }
    }
}

pub fn parse_lib_str<T: AsRef<Path>, U: AsRef<Path>, V: BuildHasher>(
    s: &str,
    path: T,
    pre_defines: &HashMap<String, Option<Define>, V>,
    include_paths: &[U],
    ignore_include: bool,
) -> Result<(SyntaxTree, Defines), Error> {
    let (text, defines) = preprocess_str(
        s,
        path,
        pre_defines,
        include_paths,
        ignore_include,
        false,
        0,
    )?;
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
        Err(x) => {
            let pos = match x {
                nom::Err::Incomplete(_) => None,
                nom::Err::Error(e) => error_position(&e),
                nom::Err::Failure(e) => error_position(&e),
            };
            let origin = if let Some(pos) = pos {
                if let Some(origin) = text.origin(pos) {
                    Some((origin.0.clone(), origin.1))
                } else {
                    None
                }
            } else {
                None
            };
            Err(Error::Parse(origin))
        }
    }
}

#[macro_export]
macro_rules! unwrap_node {
    ($n:expr, $( $ty:tt ),+) => {{
        let unwrap = || {
            for x in $n {
                match x {
                    $(sv_parser::RefNode::$ty(x) => return Some(sv_parser::RefNode::$ty(x)),)*
                    _ => (),
                }
            }
            None
        };
        unwrap()
    }};
}

#[macro_export]
macro_rules! unwrap_locate {
    ($n:expr) => {{
        let unwrap = || {
            for x in $n {
                match x {
                    sv_parser::RefNode::Locate(x) => return Some(x),
                    _ => (),
                }
            }
            None
        };
        unwrap()
    }};
}
