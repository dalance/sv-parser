#![recursion_limit = "256"]

use nom_greedyerror::error_position;
use std::fmt;
use std::hash::BuildHasher;
use std::path::{Path, PathBuf};
pub use sv_parser_error::Error;
use sv_parser_parser::{
    lib_parser, lib_parser_incomplete, sv_parser, sv_parser_incomplete, Span, SpanInfo,
};
pub use sv_parser_pp::preprocess::{
    preprocess, preprocess_str, Define, DefineText, Defines, PreprocessedText,
};
pub use sv_parser_syntaxtree::*;

pub struct SyntaxTree {
    node: AnyNode,
    text: PreprocessedText,
}

impl SyntaxTree {
    /// Get `&str` from the specified node
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

    /// Get `&str` without trailing `WhiteSpace` from the specified node
    pub fn get_str_trim<'a, T: Into<RefNodes<'a>>>(&self, nodes: T) -> Option<&str> {
        let mut beg = None;
        let mut end = 0;
        let mut skip = false;
        for n in Iter::new(nodes.into()).event() {
            match n {
                NodeEvent::Enter(RefNode::WhiteSpace(_)) => {
                    skip = true;
                }
                NodeEvent::Leave(RefNode::WhiteSpace(_)) => {
                    skip = false;
                }
                NodeEvent::Enter(RefNode::Locate(x)) if !skip => {
                    if beg.is_none() {
                        beg = Some(x.offset);
                    }
                    end = x.offset + x.len;
                }
                _ => (),
            }
        }
        if let Some(beg) = beg {
            let ret = unsafe { self.text.text().get_unchecked(beg..end) };
            Some(ret)
        } else {
            None
        }
    }

    /// Get source code location of the specified `Locate`
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

impl fmt::Debug for SyntaxTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum WS {
            NotWhitespace,
            Newline,
            Space,
            Comment,
            CompilerDirective,
        }

        let mut ws: WS = WS::NotWhitespace;
        let mut depth = 0;
        let mut ret = String::from("");
        for node in self.into_iter().event() {
            match node {
                NodeEvent::Enter(RefNode::Locate(locate)) => {
                    let (pre, t, post) = match ws {
                        WS::Newline => ("<<<<<", "NewlineToken", ">>>>>"),
                        WS::Space => ("<<<<<", "SpaceToken", ">>>>>"),
                        WS::Comment => ("<<<<<", "CommentToken", ">>>>>"),
                        _ => ("", "Token", ""),
                    };
                    ret.push_str(&format!(
                        "{}{} @line:{}: {}{}{}\n",
                        " ".repeat(depth),
                        t,
                        locate.line,
                        pre,
                        self.get_str(locate).unwrap(),
                        post,
                    ));
                    depth += 1;
                }
                NodeEvent::Enter(x) => {
                    match x {
                        RefNode::WhiteSpace(WhiteSpace::Newline(_)) => { ws = WS::Newline; }
                        RefNode::WhiteSpace(WhiteSpace::Space(_)) => { ws = WS::Space; }
                        RefNode::WhiteSpace(WhiteSpace::Comment(_)) => { ws = WS::Comment; }
                        RefNode::WhiteSpace(WhiteSpace::CompilerDirective(_)) => { ws = WS::CompilerDirective; }
                        _ => {}
                    }
                    ret.push_str(&format!("{}{}\n", " ".repeat(depth), x));
                    depth += 1;
                }
                NodeEvent::Leave(x) => {
                    match x {
                        RefNode::WhiteSpace(_) => {}
                        _ => { ws = WS::NotWhitespace; }
                    }
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
    pre_defines: &Defines<V>,
    include_paths: &[U],
    ignore_include: bool,
    allow_incomplete: bool,
) -> Result<(SyntaxTree, Defines), Error> {
    let (text, defines) = preprocess(
        path,
        pre_defines,
        include_paths,
        false, // strip_comments
        ignore_include,
    )?;
    parse_sv_pp(text, defines, allow_incomplete)
}

pub fn parse_sv_pp(
    text: PreprocessedText,
    defines: Defines,
    allow_incomplete: bool,
) -> Result<(SyntaxTree, Defines), Error> {
    let span = Span::new_extra(text.text(), SpanInfo::default());
    let result = if allow_incomplete {
        sv_parser_incomplete(span)
    } else {
        sv_parser(span)
    };
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
    pre_defines: &Defines<V>,
    include_paths: &[U],
    ignore_include: bool,
    allow_incomplete: bool,
) -> Result<(SyntaxTree, Defines), Error> {
    let (text, defines) = preprocess_str(
        s,
        path,
        pre_defines,
        include_paths,
        ignore_include,
        false, // strip_comments
        0, // resolve_depth
        0, // include_depth
    )?;
    parse_sv_pp(text, defines, allow_incomplete)
}

pub fn parse_lib<T: AsRef<Path>, U: AsRef<Path>, V: BuildHasher>(
    path: T,
    pre_defines: &Defines<V>,
    include_paths: &[U],
    ignore_include: bool,
    allow_incomplete: bool,
) -> Result<(SyntaxTree, Defines), Error> {
    let (text, defines) = preprocess(
        path,
        pre_defines,
        include_paths,
        false, // strip_comments
        ignore_include,
    )?;
    parse_lib_pp(text, defines, allow_incomplete)
}

pub fn parse_lib_str<T: AsRef<Path>, U: AsRef<Path>, V: BuildHasher>(
    s: &str,
    path: T,
    pre_defines: &Defines<V>,
    include_paths: &[U],
    ignore_include: bool,
    allow_incomplete: bool,
) -> Result<(SyntaxTree, Defines), Error> {
    let (text, defines) = preprocess_str(
        s,
        path,
        pre_defines,
        include_paths,
        ignore_include,
        false, // strip_comments
        0, // resolve_depth
        0, // include_depth
    )?;
    parse_lib_pp(text, defines, allow_incomplete)
}

pub fn parse_lib_pp(
    text: PreprocessedText,
    defines: Defines,
    allow_incomplete: bool,
) -> Result<(SyntaxTree, Defines), Error> {
    let span = Span::new_extra(text.text(), SpanInfo::default());
    let result = if allow_incomplete {
        lib_parser_incomplete(span)
    } else {
        lib_parser(span)
    };
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

/// Extracts the first matching variant from an iterator of `RefNode` values.
///
/// This macro takes an iterator (`$n`) and a list of `RefNode` variant types (`$ty`),
/// returning the first occurrence of any specified variant as `Some(RefNode::<$ty>)`.
/// If no matching variant is found, it returns `None`.
///
/// # Arguments
///
/// - `$n`: An iterator over `RefNode` values.
/// - `$ty`: One or more `RefNode` variant names to search for.
///
/// # Returns
///
/// - `Some(RefNode::<$ty>)` if a matching variant is found.
/// - `None` if no matching variant is found.
#[macro_export]
macro_rules! unwrap_node {
    ($n:expr, $( $ty:tt ),+) => {{
        let unwrap = || {
            for x in $n {
                match x {
                    $($crate::RefNode::$ty(x) => return Some($crate::RefNode::$ty(x)),)*
                    _ => (),
                }
            }
            None
        };
        unwrap()
    }};
}

/// Extracts the first `Locate` variant from an iterator of `RefNode`.
///
/// This macro takes an expression that evaluates to an iterable collection
/// of `RefNode` elements and returns the first `Locate` variant found,
/// if any. If no `Locate` variant is found, it returns `None`.
///
/// # Arguments
///
/// * `$n:expr` - An expression yielding an iterator over `RefNode` values.
///
/// # Returns
///
/// * `Option<Locate>` - The first `Locate` variant found in the iterator, or `None` if none exist.
///
#[macro_export]
macro_rules! unwrap_locate {
    ($n:expr) => {{
        let unwrap = || {
            for x in $n {
                match x {
                    $crate::RefNode::Locate(x) => return Some(x),
                    _ => (),
                }
            }
            None
        };
        unwrap()
    }};
}

#[cfg(test)]
mod test {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test() {
        let src = "/* comment */";
        let (syntax_tree, _) =
            parse_sv_str(src, PathBuf::from(""), &HashMap::new(), &[""], false, false).unwrap();
        let comment = unwrap_node!(&syntax_tree, Comment);
        assert!(comment.is_some());
    }

    #[test]
    fn test_continuous() {
        let src = r##"`ifdef A
`endif

module FetchStage();
    always_comb begin
        for (int j = i + 1; j < FETCH_WIDTH; j++) begin
        end
        break;
    end

    AddrPath fetchAddrOut;
endmodule"##;

        let src_broken = r##"`ifdef A
endif

module FetchStage();
    always_comb begin
        for (int j = i + 1; j < FETCH_WIDTH; j++) begin
        end
        break;
    end

    AddrPath fetchAddrOut;
endmodule"##;

        let path = PathBuf::from("");
        let defines = HashMap::new();
        let ret = parse_sv_str(src, &path, &defines, &[""], false, false);
        assert!(ret.is_ok());
        let ret = parse_sv_str(src_broken, &path, &defines, &[""], false, false);
        assert!(ret.is_err());
        let ret = parse_sv_str(src, &path, &defines, &[""], false, false);
        assert!(ret.is_ok());
        let ret = parse_sv_str(src_broken, &path, &defines, &[""], false, false);
        assert!(ret.is_err());
        let ret = parse_sv_str(src, &path, &defines, &[""], false, false);
        assert!(ret.is_ok());
    }
}
