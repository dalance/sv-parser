use crate::range::Range;
use nom::combinator::all_consuming;
use nom_greedyerror::error_position;
use std::collections::{BTreeMap, HashMap};
use std::convert::TryInto;
use std::fs::File;
use std::hash::BuildHasher;
use std::io::{BufReader, Read};
use std::path::{Path, PathBuf};
use sv_parser_error::Error;
use sv_parser_parser::{pp_parser, Span, SpanInfo};
use sv_parser_syntaxtree::{
    IncludeCompilerDirective, Locate, NodeEvent, RefNode, SourceDescription, TextMacroUsage,
    WhiteSpace,
};
use std::collections::hash_map::RandomState;

const RECURSIVE_LIMIT: usize = 64;

#[derive(Debug)]
pub struct PreprocessedText {
    text: String,
    origins: BTreeMap<Range, Origin>,
}

#[derive(Debug)]
pub struct Origin {
    range: Range,
    origin: Option<(PathBuf, Range)>,
}

impl PreprocessedText {
    fn new() -> Self {
        PreprocessedText {
            text: String::new(),
            origins: BTreeMap::new(),
        }
    }

    fn push<T: AsRef<Path>>(&mut self, s: &str, origin: Option<(T, Range)>) {
        let base = self.text.len();
        self.text.push_str(s);

        let origin = if let Some((origin_path, origin_range)) = origin {
            let origin_path = PathBuf::from(origin_path.as_ref());
            Some((origin_path, origin_range))
        } else {
            None
        };

        let range = Range::new(base, base + s.len());
        let origin = Origin { range, origin };
        self.origins.insert(range, origin);
    }

    fn merge(&mut self, other: PreprocessedText) {
        let base = self.text.len();
        self.text.push_str(&other.text);
        for (mut range, mut origin) in other.origins {
            range.offset(base);
            origin.range.offset(base);
            self.origins.insert(range, origin);
        }
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn origin(&self, pos: usize) -> Option<(&PathBuf, usize)> {
        let origin = self.origins.get(&Range::new(pos, pos + 1));
        if let Some(origin) = origin {
            if let Some((ref origin_path, ref origin_range)) = origin.origin {
                let ret_pos = pos - origin.range.begin + origin_range.begin;
                Some((&origin_path, ret_pos))
            } else {
                None
            }
        } else {
            None
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Define {
    pub identifier: String,
    pub arguments: Vec<(String, Option<String>)>,
    pub text: Option<DefineText>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DefineText {
    pub text: String,
    pub origin: Option<(PathBuf, Range)>,
}

impl Define {
    pub fn new(
        ident: String,
        args: Vec<(String, Option<String>)>,
        text: Option<DefineText>,
    ) -> Self {
        Define {
            identifier: ident,
            arguments: args,
            text,
        }
    }
}

impl DefineText {
    pub fn new(text: String, origin: Option<(PathBuf, Range)>) -> Self {
        DefineText { text, origin }
    }
}

pub type Defines<V=RandomState> = HashMap<String, Option<Define>, V>;

pub fn preprocess<T: AsRef<Path>, U: AsRef<Path>, V: BuildHasher>(
    path: T,
    pre_defines: &Defines<V>,
    include_paths: &[U],
    strip_comments: bool,
    ignore_include: bool,
) -> Result<(PreprocessedText, Defines), Error> {
    let f = File::open(path.as_ref()).map_err(|x| Error::File {
        source: x,
        path: PathBuf::from(path.as_ref()),
    })?;
    let mut reader = BufReader::new(f);
    let mut s = String::new();
    reader.read_to_string(&mut s)?;

    preprocess_str(
        &s,
        path,
        pre_defines,
        include_paths,
        ignore_include,
        strip_comments,
        0,
    )
}

struct SkipNodes<'a> {
    nodes: Vec<RefNode<'a>>,
}

impl<'a> SkipNodes<'a> {
    fn new() -> Self {
        Self { nodes: vec![] }
    }

    fn push(&mut self, node: RefNode<'a>) {
        // if a node doesn't have locate, the node should be ignored
        // because the node can be identified in tree.
        let mut have_locate = false;
        for x in node.clone() {
            if let RefNode::Locate(_) = x {
                have_locate = true;
            }
        }
        if have_locate {
            self.nodes.push(node);
        }
    }

    fn contains(&self, node: &RefNode<'a>) -> bool {
        self.nodes.contains(node)
    }
}

pub fn preprocess_str<T: AsRef<Path>, U: AsRef<Path>, V: BuildHasher>(
    s: &str,
    path: T,
    pre_defines: &Defines<V>,
    include_paths: &[U],
    ignore_include: bool,
    strip_comments: bool,
    resolve_depth: usize,
) -> Result<(PreprocessedText, Defines), Error> {
    let mut skip = false;
    let mut skip_nodes = SkipNodes::new();
    let mut defines = HashMap::new();

    let mut last_item_line = None;
    let mut last_include_line = None;

    for (k, v) in pre_defines {
        defines.insert(k.clone(), (*v).clone());
    }

    let span = Span::new_extra(&s, SpanInfo::default());
    let (_, pp_text) = all_consuming(pp_parser)(span).map_err(|x| match x {
        nom::Err::Incomplete(_) => Error::Parse(None),
        nom::Err::Error(e) => {
            if let Some(pos) = error_position(&e) {
                Error::Parse(Some((PathBuf::from(path.as_ref()), pos)))
            } else {
                Error::Parse(None)
            }
        }
        nom::Err::Failure(e) => {
            if let Some(pos) = error_position(&e) {
                Error::Parse(Some((PathBuf::from(path.as_ref()), pos)))
            } else {
                Error::Parse(None)
            }
        }
    })?;

    let mut ret = PreprocessedText::new();

    for n in pp_text.into_iter().event() {
        match n.clone() {
            NodeEvent::Enter(x) => {
                if skip_nodes.contains(&x) {
                    skip = true;
                }
            }
            NodeEvent::Leave(x) => {
                if skip_nodes.contains(&x) {
                    skip = false;
                }
            }
        }
        if skip {
            continue;
        }

        match n.clone() {
            NodeEvent::Enter(RefNode::SourceDescriptionNotDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                if let Some(last_include_line) = last_include_line {
                    if last_include_line == locate.line {
                        return Err(Error::IncludeLine);
                    }
                }
            }
            NodeEvent::Enter(RefNode::CompilerDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                if let Some(last_include_line) = last_include_line {
                    if last_include_line == locate.line {
                        return Err(Error::IncludeLine);
                    }
                }
            }
            NodeEvent::Leave(RefNode::SourceDescriptionNotDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                // If the item is whitespace, last_item_line should not be updated
                if !locate.str(s).trim().is_empty() {
                    last_item_line = Some(locate.line);
                }
            }
            NodeEvent::Leave(RefNode::CompilerDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                last_item_line = Some(locate.line);
            }
            _ => (),
        }
        match n {
            NodeEvent::Enter(RefNode::SourceDescriptionNotDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
            }
            NodeEvent::Enter(RefNode::SourceDescription(SourceDescription::StringLiteral(x))) => {
                let locate: Locate = (&**x).try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
            }
            NodeEvent::Enter(RefNode::SourceDescription(SourceDescription::EscapedIdentifier(
                x,
            ))) => {
                let locate: Locate = (&**x).try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
            }
            NodeEvent::Enter(RefNode::ResetallCompilerDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
            }
            NodeEvent::Enter(RefNode::TimescaleCompilerDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
            }
            NodeEvent::Enter(RefNode::DefaultNettypeCompilerDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
            }
            NodeEvent::Enter(RefNode::UnconnectedDriveCompilerDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
            }
            NodeEvent::Enter(RefNode::NounconnectedDriveCompilerDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
            }
            NodeEvent::Enter(RefNode::CelldefineDriveCompilerDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
            }
            NodeEvent::Enter(RefNode::EndcelldefineDriveCompilerDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
            }
            NodeEvent::Enter(RefNode::Pragma(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
            }
            NodeEvent::Enter(RefNode::LineCompilerDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
            }
            NodeEvent::Enter(RefNode::KeywordsDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
            }
            NodeEvent::Enter(RefNode::EndkeywordsDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
            }
            NodeEvent::Enter(RefNode::UndefineCompilerDirective(x)) => {
                skip_nodes.push(x.into());
                skip = true;

                let (_, _, ref name) = x.nodes;
                let id = identifier((&name.nodes.0).into(), &s).unwrap();
                defines.remove(&id);
            }
            NodeEvent::Enter(RefNode::UndefineallCompilerDirective(x)) => {
                skip_nodes.push(x.into());
                skip = true;

                defines.clear();
            }
            NodeEvent::Enter(RefNode::IfdefDirective(x)) => {
                let (_, ref keyword, ref ifid, ref ifbody, ref elsif, ref elsebody, _, _) = x.nodes;
                skip_nodes.push(keyword.into());
                skip_nodes.push(ifid.into());

                let ifid = identifier(ifid.into(), &s).unwrap();
                let mut hit = false;
                if defines.contains_key(&ifid) {
                    hit = true;
                } else {
                    skip_nodes.push(ifbody.into());
                }

                for x in elsif {
                    let (_, ref keyword, ref elsifid, ref elsifbody) = x;
                    skip_nodes.push(keyword.into());
                    skip_nodes.push(elsifid.into());

                    let elsifid = identifier(elsifid.into(), &s).unwrap();
                    if hit {
                        skip_nodes.push(elsifbody.into());
                    } else if defines.contains_key(&elsifid) {
                        hit = true;
                    } else {
                        skip_nodes.push(elsifbody.into());
                    }
                }

                if let Some(elsebody) = elsebody {
                    let (_, ref keyword, ref elsebody) = elsebody;
                    skip_nodes.push(keyword.into());
                    if hit {
                        skip_nodes.push(elsebody.into());
                    }
                }
            }
            NodeEvent::Enter(RefNode::WhiteSpace(x)) if !strip_comments => {
                if let WhiteSpace::Space(_) = x {
                    let locate: Locate = x.try_into().unwrap();
                    let range = Range::new(locate.offset + locate.len, locate.offset + locate.len);
                    ret.push(locate.str(&s), Some((path.as_ref(), range)));
                }
            }
            NodeEvent::Enter(RefNode::Comment(x)) if !strip_comments => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
            }
            NodeEvent::Enter(RefNode::IfndefDirective(x)) => {
                let (_, ref keyword, ref ifid, ref ifbody, ref elsif, ref elsebody, _, _) = x.nodes;
                skip_nodes.push(keyword.into());
                skip_nodes.push(ifid.into());

                let ifid = identifier(ifid.into(), &s).unwrap();
                let mut hit = false;
                if !defines.contains_key(&ifid) {
                    hit = true;
                } else {
                    skip_nodes.push(ifbody.into());
                }

                for x in elsif {
                    let (_, ref keyword, ref elsifid, ref elsifbody) = x;
                    skip_nodes.push(keyword.into());
                    skip_nodes.push(elsifid.into());

                    let elsifid = identifier(elsifid.into(), &s).unwrap();
                    if hit {
                        skip_nodes.push(elsifbody.into());
                    } else if defines.contains_key(&elsifid) {
                        hit = true;
                    } else {
                        skip_nodes.push(elsifbody.into());
                    }
                }

                if let Some(elsebody) = elsebody {
                    let (_, ref keyword, ref elsebody) = elsebody;
                    skip_nodes.push(keyword.into());
                    if hit {
                        skip_nodes.push(elsebody.into());
                    }
                }
            }
            NodeEvent::Enter(RefNode::TextMacroDefinition(x)) => {
                skip_nodes.push(x.into());
                skip = true;

                let (_, _, ref proto, ref text) = x.nodes;
                let (ref name, ref args) = proto.nodes;
                let id = identifier(name.into(), &s).unwrap();

                let mut define_args = Vec::new();
                if let Some(args) = args {
                    let (_, ref args, _) = args.nodes;
                    let (ref args,) = args.nodes;
                    for arg in args.contents() {
                        let (ref arg, ref default) = arg.nodes;
                        let (ref arg, _) = arg.nodes;
                        let arg = String::from(arg.str(&s));

                        let default = if let Some((_, x)) = default {
                            let x: Locate = x.try_into().unwrap();
                            let x = String::from(x.str(&s));
                            Some(x)
                        } else {
                            None
                        };

                        define_args.push((arg, default));
                    }
                }

                let define_text = if let Some(text) = text {
                    let text: Locate = text.try_into().unwrap();
                    let range = Range::new(text.offset, text.offset + text.len);
                    let text = String::from(text.str(&s));
                    Some(DefineText {
                        text,
                        origin: Some((PathBuf::from(path.as_ref()), range)),
                    })
                } else {
                    None
                };

                let define = Define {
                    identifier: id.clone(),
                    arguments: define_args,
                    text: define_text,
                };

                defines.insert(id, Some(define));

                // Keep TextMacroDefinition after preprocess
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
            }
            NodeEvent::Enter(RefNode::IncludeCompilerDirective(x)) if !ignore_include => {
                skip_nodes.push(x.into());
                skip = true;

                let locate: Locate = x.try_into().unwrap();
                last_include_line = Some(locate.line);

                if let Some(last_item_line) = last_item_line {
                    if last_item_line == locate.line {
                        return Err(Error::IncludeLine);
                    }
                }

                let mut path = match x {
                    IncludeCompilerDirective::DoubleQuote(x) => {
                        let (_, ref keyword, ref literal) = x.nodes;
                        skip_nodes.push(keyword.into());

                        let (locate, _) = literal.nodes;
                        let p = locate.str(&s).trim_matches('"');
                        PathBuf::from(p)
                    }
                    IncludeCompilerDirective::AngleBracket(x) => {
                        let (_, ref keyword, ref literal) = x.nodes;
                        skip_nodes.push(keyword.into());

                        let (locate, _) = literal.nodes;
                        let p = locate.str(&s).trim_start_matches('<').trim_end_matches('>');
                        PathBuf::from(p)
                    }
                    IncludeCompilerDirective::TextMacroUsage(x) => {
                        let (_, ref keyword, ref x) = x.nodes;
                        skip_nodes.push(keyword.into());
                        skip_nodes.push(x.into());

                        if let Some((p, _, _)) = resolve_text_macro_usage(
                            x,
                            s,
                            path.as_ref(),
                            &defines,
                            include_paths,
                            strip_comments,
                            resolve_depth + 1,
                        )? {
                            let p = p.trim().trim_matches('"');
                            PathBuf::from(p)
                        } else {
                            PathBuf::from("")
                        }
                    }
                };
                if path.is_relative() && !path.exists() {
                    for include_path in include_paths {
                        let new_path = include_path.as_ref().join(&path);
                        if new_path.exists() {
                            path = new_path;
                            break;
                        }
                    }
                }
                let (include, new_defines) =
                    preprocess(path, &defines, include_paths, strip_comments, false).map_err(
                        |x| Error::Include {
                            source: Box::new(x),
                        },
                    )?;
                defines = new_defines;
                ret.merge(include);
            }
            NodeEvent::Enter(RefNode::TextMacroUsage(x)) => {
                skip_nodes.push(x.into());
                skip = true;

                if let Some((text, origin, new_defines)) = resolve_text_macro_usage(
                    x,
                    s,
                    path.as_ref(),
                    &defines,
                    include_paths,
                    strip_comments,
                    resolve_depth + 1,
                )? {
                    ret.push(&text, origin);
                    defines = new_defines;
                }
            }
            NodeEvent::Enter(RefNode::PositionCompilerDirective(x)) => {
                skip_nodes.push(x.into());
                skip = true;

                let (_, ref x) = x.nodes;
                let locate: Locate = x.try_into().unwrap();
                let x = locate.str(s);
                if x.starts_with("__FILE__") {
                    ret.push::<PathBuf>(
                        &x.replace(
                            "__FILE__",
                            &format!("\"{}\"", path.as_ref().to_string_lossy()),
                        ),
                        None,
                    );
                } else if x.starts_with("__LINE__") {
                    ret.push::<PathBuf>(&x.replace("__LINE__", &format!("{}", locate.line)), None);
                }
            }
            _ => (),
        }
    }

    Ok((ret, defines))
}

fn identifier(node: RefNode, s: &str) -> Option<String> {
    for x in node {
        match x {
            RefNode::SimpleIdentifier(x) => {
                let x: Locate = x.nodes.0.try_into().unwrap();
                return Some(String::from(x.str(s)));
            }
            RefNode::EscapedIdentifier(x) => {
                let x: Locate = x.nodes.0.try_into().unwrap();
                let x = x.str(s);
                let x = &x[1..]; // remove \
                return Some(String::from(x));
            }
            _ => (),
        }
    }
    None
}

fn get_str(node: RefNode, s: &str) -> String {
    let mut ret = String::from("");
    for x in node {
        match x {
            RefNode::Locate(x) => {
                ret.push_str(x.str(s));
            }
            _ => (),
        }
    }
    ret
}

fn split_text(s: &str) -> Vec<String> {
    let mut is_string = false;
    let mut is_ident = false;
    let mut is_backquote_prev = false;
    let mut is_comment = false;
    let mut is_ident_prev;
    let mut x = String::from("");
    let mut ret = vec![];

    let mut iter = s.chars().peekable();
    while let Some(c) = iter.next() {
        is_ident_prev = is_ident;
        is_ident = c.is_ascii_alphanumeric() | (c == '_');

        if c == '\n' && is_comment {
            is_comment = false;
            x.push(c);
        } else if is_comment {
            continue;
        } else if c == '"' && is_backquote_prev {
            x.push(c);
            ret.push(x);
            x = String::from("");
        } else if c == '"' && !is_string {
            ret.push(x);
            x = String::from("");
            x.push(c);
            is_string = true;
        } else if c == '"' && is_string {
            x.push(c);
            ret.push(x);
            x = String::from("");
            is_string = false;
        } else if c == '/' && iter.peek() == Some(&'/') && !is_string {
            is_comment = true;
        } else if !is_string {
            if is_ident != is_ident_prev {
                ret.push(x);
                x = String::from("");
            }
            x.push(c);
        } else {
            x.push(c);
        }

        is_backquote_prev = c == '`';
    }
    ret.push(x);
    ret
}

fn resolve_text_macro_usage<T: AsRef<Path>, U: AsRef<Path>>(
    x: &TextMacroUsage,
    s: &str,
    path: T,
    defines: &Defines,
    include_paths: &[U],
    strip_comments: bool,
    resolve_depth: usize,
) -> Result<Option<(String, Option<(PathBuf, Range)>, Defines)>, Error> {
    let (_, ref name, ref args) = x.nodes;
    let id = identifier((&name.nodes.0).into(), &s).unwrap();

    if resolve_depth > RECURSIVE_LIMIT {
        return Err(Error::ExceedRecursiveLimit);
    }

    let mut args_str = String::from("");
    let mut actual_args = Vec::new();
    let no_args = args.is_none();
    if let Some(args) = args {
        args_str.push_str(&get_str((&args.nodes.0).into(), s));
        args_str.push_str(&get_str((&args.nodes.1).into(), s));
        args_str.push_str(&get_str((&args.nodes.2).into(), s));

        let (_, ref args, _) = args.nodes;
        let (ref args,) = args.nodes;
        for arg in args.contents() {
            if let Some(arg) = arg {
                let (ref arg,) = arg.nodes;
                let arg = arg.str(&s).trim_end();
                actual_args.push(Some(arg));
            } else {
                actual_args.push(None);
            }
        }
    }

    let define = defines.get(&id);
    if let Some(Some(define)) = define {
        let mut arg_map = HashMap::new();

        if !define.arguments.is_empty() && no_args {
            return Err(Error::DefineNoArgs);
        }

        for (i, (arg, default)) in define.arguments.iter().enumerate() {
            let value = match actual_args.get(i) {
                Some(Some(actual_arg)) => *actual_arg,
                Some(None) => {
                    if let Some(default) = default {
                        default
                    } else {
                        ""
                    }
                }
                None => {
                    if let Some(default) = default {
                        default
                    } else {
                        return Err(Error::DefineArgNotFound(String::from(arg)));
                    }
                }
            };
            arg_map.insert(String::from(arg), value);
        }

        // restore () for textmacro without arguments
        let paren = if define.arguments.is_empty() {
            Some(args_str)
        } else {
            None
        };

        if let Some(ref text) = define.text {
            let mut replaced = String::from("");
            for text in split_text(&text.text) {
                if let Some(value) = arg_map.get(&text) {
                    replaced.push_str(*value);
                } else {
                    replaced.push_str(
                        &text
                            .replace("``", "")
                            .replace("`\\`\"", "\\\"")
                            .replace("`\"", "\"")
                            .replace("\\\n", "\n")
                            .replace("\\\r\n", "\r\n")
                            .replace("\\\r", "\r"),
                    );
                }
            }

            if let Some(paren) = paren {
                replaced.push_str(&paren);
            }

            // separator is required
            replaced.push_str(" ");
            // remove leading whitespace
            replaced = String::from(replaced.trim_start());
            let (replaced, new_defines) = preprocess_str(
                &replaced,
                path.as_ref(),
                &defines,
                include_paths,
                false,
                strip_comments,
                resolve_depth,
            )?;
            Ok(Some((
                String::from(replaced.text()),
                text.origin.clone(),
                new_defines,
            )))
        } else {
            Ok(None)
        }
    } else if define.is_some() {
        Ok(None)
    } else {
        Err(Error::DefineNotFound(id))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::env;

    fn get_testcase(s: &str) -> String {
        format!(
            "{}/testcases/{}",
            env::var("CARGO_MANIFEST_DIR").unwrap(),
            s
        )
    }

    #[test]
    fn test1() {
        let (ret, _) = preprocess(
            get_testcase("test1.sv"),
            &HashMap::new(),
            &[] as &[String],
            false,
            false,
        )
        .unwrap();
        assert_eq!(
            ret.text(),
            r##"module and_op (a, b, c);
output a;
input b, c;

and a1 (a,b,c);

endmodule
"##
        );
        assert_eq!(
            ret.origin(10).unwrap().0,
            &PathBuf::from(get_testcase("test1.sv"))
        );
        assert_eq!(ret.origin(10).unwrap().1, 10);
        assert_eq!(ret.origin(50).unwrap().1, 98);
        assert_eq!(ret.origin(70).unwrap().1, 124);
    }

    #[test]
    fn test1_predefine() {
        let mut defines = HashMap::new();
        defines.insert(String::from("behavioral"), None);
        let (ret, _) = preprocess(
            get_testcase("test1.sv"),
            &defines,
            &[] as &[String],
            false,
            false,
        )
        .unwrap();
        assert_eq!(
            ret.text(),
            r##"module and_op (a, b, c);
output a;
input b, c;

wire a = b & c;

endmodule
"##
        )
    }

    #[test]
    fn test2() {
        let include_paths = [get_testcase("")];
        let (ret, _) = preprocess(
            get_testcase("test2.sv"),
            &HashMap::new(),
            &include_paths,
            false,
            false,
        )
        .unwrap();
        assert_eq!(
            ret.text(),
            r##"module and_op (a, b, c);
output a;
input b, c;

and a1 (a,b,c);


endmodule
"##
        );
        assert_eq!(
            ret.origin(10).unwrap().0,
            &PathBuf::from(get_testcase("test2.sv"))
        );
        assert_eq!(ret.origin(10).unwrap().1, 10);
        assert_eq!(
            ret.origin(50).unwrap().0,
            &PathBuf::from(get_testcase("test2.svh"))
        );
        assert_eq!(ret.origin(50).unwrap().1, 73);
        assert_eq!(
            ret.origin(70).unwrap().0,
            &PathBuf::from(get_testcase("test2.sv"))
        );
        assert_eq!(ret.origin(70).unwrap().1, 50);
    }

    #[test]
    fn test2_ignore_include() {
        let include_paths = [get_testcase("")];
        let (ret, _) = preprocess(
            get_testcase("test2.sv"),
            &HashMap::new(),
            &include_paths,
            false,
            true,
        )
        .unwrap();
        assert_eq!(
            ret.text(),
            r##"module and_op (a, b, c);
 
endmodule
"##
        );
    }

    #[test]
    fn test3() {
        let (ret, _) = preprocess(
            get_testcase("test3.sv"),
            &HashMap::new(),
            &[] as &[String],
            false,
            false,
        )
        .unwrap();
        assert_eq!(
            ret.text(),
            r##"`define connect(NAME, INDEX = 0) \
  assign NAME``_``INDEX``__x = NAME[INDEX].x; \
  assign NAME``_``INDEX``__y = NAME[INDEX].y;

module a ();

  assign a_0__x = a[0].x; 
  assign a_0__y = a[0].y; assign a_1__x = a[1].x; 
  assign a_1__y = a[1].y; endmodule
"##
        );
    }

    #[test]
    fn test4() {
        let (ret, _) = preprocess(
            get_testcase("test4.sv"),
            &HashMap::new(),
            &[] as &[String],
            false,
            false,
        )
        .unwrap();
        assert_eq!(
            ret.text(),
            r##"`define disp(clk, exp, msg) \
    always @(posedge clk) begin \
        if (!(exp)) begin \
            $display msg; \
        end \
    end \

module a ();

always @(posedge clk) begin 
        if (!(!(a[i].b && c[i]))) begin 
            $display ("xxx(()[]]{}}}", a[i].b, c[i]); 
        end 
    end 
 ;

endmodule
"##
        );
    }

    #[test]
    fn test5() {
        let (ret, _) = preprocess(
            get_testcase("test5.sv"),
            &HashMap::new(),
            &[] as &[String],
            false,
            false,
        )
        .unwrap();
        assert_eq!(
            ret.text(),
            r##"module a;
`define HI Hello
`define LO "`HI, world"
`define H(x) "Hello, x"
initial begin
$display("`HI, world");
$display("`HI, world"  );
$display("Hello, x"  );
end
endmodule
"##
        );
    }

    #[test]
    fn test6() {
        let (ret, _) = preprocess(
            get_testcase("test6.sv"),
            &HashMap::new(),
            &[] as &[String],
            false,
            false,
        )
        .unwrap();
        assert_eq!(
            ret.text(),
            r##"`define msg(x,y) `"x: `\`"y`\`"`"

module a;
initial begin
$display("left side: \"right side\""  );
end
endmodule
"##
        );
    }

    #[test]
    fn test7() {
        let ret = preprocess(
            get_testcase("test7.sv"),
            &HashMap::new(),
            &[] as &[String],
            false,
            false,
        );
        assert_eq!(format!("{:?}", ret), "Err(ExceedRecursiveLimit)");
    }

    #[test]
    fn test8() {
        let ret = preprocess(
            get_testcase("test8.sv"),
            &HashMap::new(),
            &[] as &[String],
            false,
            false,
        );
        assert_eq!(format!("{:?}", ret), "Err(ExceedRecursiveLimit)");
    }

    #[test]
    fn test9() {
        let include_paths = [get_testcase("")];
        let ret = preprocess(
            get_testcase("test9.sv"),
            &HashMap::new(),
            &include_paths,
            false,
            false,
        );
        assert_eq!(format!("{:?}", ret), "Err(IncludeLine)");
    }

    #[test]
    fn test10() {
        let include_paths = [get_testcase("")];
        let ret = preprocess(
            get_testcase("test10.sv"),
            &HashMap::new(),
            &include_paths,
            false,
            false,
        );
        assert_eq!(format!("{:?}", ret), "Err(IncludeLine)");
    }

    #[test]
    fn test11() {
        let (ret, _) = preprocess(
            get_testcase("test11.sv"),
            &HashMap::new(),
            &[] as &[String],
            false,
            false,
        )
        .unwrap();
        assert_eq!(
            ret.text(),
            r##"module a;
initial begin
    if (3 == 0) begin
    end
end
endmodule
"##
        );
    }

    #[test]
    fn test12() {
        let (ret, _) = preprocess(
            get_testcase("test12.sv"),
            &HashMap::new(),
            &[] as &[String],
            false,
            false,
        )
        .unwrap();
        assert_eq!(
            ret.text(),
            r##"module a;
reg \`~!-_=+\|[]{};:'"",./<>?  ;
endmodule
"##
        );
    }

    #[test]
    fn test13() {
        let (ret, _) = preprocess(
            get_testcase("test13.sv"),
            &HashMap::new(),
            &[] as &[String],
            false,
            false,
        )
        .unwrap();
        assert_eq!(
            ret.text(),
            r##"`define NAME 42 // Comment
interface foo #(WIDTH = 42  ) ();
endinterface
"##
        );
    }

    #[test]
    fn test14() {
        let (ret, _) = preprocess(
            get_testcase("test14.sv"),
            &HashMap::new(),
            &[] as &[String],
            false,
            false,
        )
        .unwrap();
        assert_eq!(
            ret.text(),
            r##"module A;
wire a = 1'b0;


endmodule
"##
        );
    }

    #[test]
    fn test15() {
        let (ret, _) = preprocess(
            get_testcase("test15.sv"),
            &HashMap::new(),
            &[] as &[String],
            false,
            false,
        )
        .unwrap();
        assert_eq!(
            ret.text(),
            r##"`define MOD_INST u_mysubmod
module mymod;
mysubmod u_mysubmod() ;
endmodule
"##
        );
    }

    #[test]
    fn test16() {
        let (ret, _) = preprocess(
            get_testcase("test16.sv"),
            &HashMap::new(),
            &[] as &[String],
            false,
            false,
        )
        .unwrap();
        assert_eq!(
            ret.text(),
            r##"module a;
`define HELLO0 "HELLO"
`define \HELLO1 "HELLO"
initial begin
$display("HELLO"  );
$display("HELLO"  );
$display("HELLO"  );
$display("HELLO"  );
end
endmodule
"##
        );
    }

    #[test]
    fn test17() {
        let (ret, _) = preprocess(
            get_testcase("test17.sv"),
            &HashMap::new(),
            &[] as &[String],
            false,
            false,
        )
        .unwrap();
        assert_eq!(
            ret.text(),
            r##"`define A \
  initial begin // comment \
  end

module test();

initial begin 
  end endmodule
"##
        );
    }

    #[test]
    fn test18() {
        let (ret, _) = preprocess(
            get_testcase("test18.sv"),
            &HashMap::new(),
            &[] as &[String],
            false,
            false,
        )
        .unwrap();
        assert_eq!(
            ret.text(),
            r##"// pragma translate_off
module A;
endmodule
// pragma translate_on

"##
        );
    }

    #[test]
    fn test19() {
        let include_paths = [get_testcase("")];
        let (ret, _) = preprocess(
            get_testcase("test19.sv"),
            &HashMap::new(),
            &include_paths,
            false,
            false,
        )
        .unwrap();
        assert_eq!(
            ret.text(),
            r##"module and_op (a, b, c);
output a;
input b, c;

and a1 (a,b,c);

 // comment
endmodule
"##
        );
        assert_eq!(
            ret.origin(10).unwrap().0,
            &PathBuf::from(get_testcase("test19.sv"))
        );
        assert_eq!(ret.origin(10).unwrap().1, 10);
        assert_eq!(
            ret.origin(50).unwrap().0,
            &PathBuf::from(get_testcase("test2.svh"))
        );
        assert_eq!(ret.origin(50).unwrap().1, 73);
        assert_eq!(
            ret.origin(70).unwrap().0,
            &PathBuf::from(get_testcase("test19.sv"))
        );
        assert_eq!(ret.origin(70).unwrap().1, 50);
    }

    #[test]
    fn test20() {
        let include_paths = [get_testcase("")];
        let (ret, _) = preprocess(
            get_testcase("test20.sv"),
            &HashMap::new(),
            &include_paths,
            false,
            false,
        )
        .unwrap();
        assert_eq!(
            ret.text(),
            r##"module and_op (a, b, c);
  // a
  output a;
input b, c;

and a1 (a,b,c);


endmodule
"##
        );
        assert_eq!(
            ret.origin(10).unwrap().0,
            &PathBuf::from(get_testcase("test20.sv"))
        );
        assert_eq!(ret.origin(10).unwrap().1, 10);
        assert_eq!(
            ret.origin(60).unwrap().0,
            &PathBuf::from(get_testcase("test2.svh"))
        );
        assert_eq!(ret.origin(60).unwrap().1, 74);
        assert_eq!(
            ret.origin(80).unwrap().0,
            &PathBuf::from(get_testcase("test20.sv"))
        );
        assert_eq!(ret.origin(80).unwrap().1, 60);
    }
}
