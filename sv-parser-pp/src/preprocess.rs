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
    preprocess_inner(
        path,
        pre_defines,
        include_paths,
        strip_comments,
        ignore_include,
        0, // include_depth
    )
}

fn preprocess_inner<T: AsRef<Path>, U: AsRef<Path>, V: BuildHasher>(
    path: T,
    pre_defines: &Defines<V>,
    include_paths: &[U],
    strip_comments: bool,
    ignore_include: bool,
    include_depth: usize,
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
        0, // resolve_depth
        include_depth,
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
    include_depth: usize,
) -> Result<(PreprocessedText, Defines), Error> {

    // IEEE1800-2017 Clause 22.4, page 675
    // A file included in the source using the `include compiler directive
    // may contain other `include compiler directives.
    // The number of nesting levels for include files shall be finite.
    // Implementations may limit the maximum number of levels to which
    // include files can be nested, but the limit shall be at least 15.
    if include_depth > RECURSIVE_LIMIT {
        return Err(Error::ExceedRecursiveLimit);
    }

    let mut skip = false;
    let mut skip_whitespace = false;
    let mut skip_nodes = SkipNodes::new();
    let mut defines = HashMap::new();

    let mut last_item_line = None;
    let mut last_include_line = None;

    for (k, v) in pre_defines {
        defines.insert(k.clone(), (*v).clone());
    }

    let span = Span::new_extra(&s, SpanInfo::default());
    let (_, pp_text) = all_consuming(pp_parser)(span).map_err(|x| match x {
        nom::Err::Incomplete(_) => Error::Preprocess(None),
        nom::Err::Error(e) => {
            if let Some(pos) = error_position(&e) {
                Error::Preprocess(Some((PathBuf::from(path.as_ref()), pos)))
            } else {
                Error::Preprocess(None)
            }
        }
        nom::Err::Failure(e) => {
            if let Some(pos) = error_position(&e) {
                Error::Preprocess(Some((PathBuf::from(path.as_ref()), pos)))
            } else {
                Error::Preprocess(None)
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
                skip_whitespace = true;
            }
            NodeEvent::Leave(RefNode::ResetallCompilerDirective(_)) => {
                skip_whitespace = false;
            }
            NodeEvent::Enter(RefNode::TimescaleCompilerDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
                skip_whitespace = true;
            }
            NodeEvent::Leave(RefNode::TimescaleCompilerDirective(_)) => {
                skip_whitespace = false;
            }
            NodeEvent::Enter(RefNode::DefaultNettypeCompilerDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
                skip_whitespace = true;
            }
            NodeEvent::Leave(RefNode::DefaultNettypeCompilerDirective(_)) => {
                skip_whitespace = false;
            }
            NodeEvent::Enter(RefNode::UnconnectedDriveCompilerDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
                skip_whitespace = true;
            }
            NodeEvent::Leave(RefNode::UnconnectedDriveCompilerDirective(_)) => {
                skip_whitespace = false;
            }
            NodeEvent::Enter(RefNode::NounconnectedDriveCompilerDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
                skip_whitespace = true;
            }
            NodeEvent::Leave(RefNode::NounconnectedDriveCompilerDirective(_)) => {
                skip_whitespace = false;
            }
            NodeEvent::Enter(RefNode::CelldefineDriveCompilerDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
                skip_whitespace = true;
            }
            NodeEvent::Leave(RefNode::CelldefineDriveCompilerDirective(_)) => {
                skip_whitespace = false;
            }
            NodeEvent::Enter(RefNode::EndcelldefineDriveCompilerDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
                skip_whitespace = true;
            }
            NodeEvent::Leave(RefNode::EndcelldefineDriveCompilerDirective(_)) => {
                skip_whitespace = false;
            }
            NodeEvent::Enter(RefNode::Pragma(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
                skip_whitespace = true;
            }
            NodeEvent::Leave(RefNode::Pragma(_)) => {
                skip_whitespace = false;
            }
            NodeEvent::Enter(RefNode::LineCompilerDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
                skip_whitespace = true;
            }
            NodeEvent::Leave(RefNode::LineCompilerDirective(_)) => {
                skip_whitespace = false;
            }
            NodeEvent::Enter(RefNode::KeywordsDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
                skip_whitespace = true;
            }
            NodeEvent::Leave(RefNode::KeywordsDirective(_)) => {
                skip_whitespace = false;
            }
            NodeEvent::Enter(RefNode::EndkeywordsDirective(x)) => {
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
                skip_whitespace = true;
            }
            NodeEvent::Leave(RefNode::EndkeywordsDirective(_)) => {
                skip_whitespace = false;
            }
            NodeEvent::Enter(RefNode::UndefineCompilerDirective(x)) => {
                let (_, _, ref name) = x.nodes;
                let id = identifier((&name.nodes.0).into(), &s).unwrap();
                defines.remove(&id);

                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
                skip_whitespace = true;
            }
            NodeEvent::Leave(RefNode::UndefineCompilerDirective(_)) => {
                skip_whitespace = false;
            }
            NodeEvent::Enter(RefNode::UndefineallCompilerDirective(x)) => {
                defines.clear();

                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
                skip_whitespace = true;
            }
            NodeEvent::Leave(RefNode::UndefineallCompilerDirective(_)) => {
                skip_whitespace = false;
            }
            NodeEvent::Enter(RefNode::IfdefDirective(x)) => {
                let (_, ref keyword, ref ifid, ref ifbody, ref elsif, ref elsebody, _, _) = x.nodes;
                skip_nodes.push(keyword.into());
                skip_nodes.push(ifid.into());

                let ifid = identifier(ifid.into(), &s).unwrap();
                let mut hit = false;
                if defines.contains_key(&ifid) || is_predefined_text_macro(&ifid) {
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
                    } else if defines.contains_key(&elsifid) || is_predefined_text_macro(&ifid) {
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
            NodeEvent::Enter(RefNode::WhiteSpace(x)) if !skip_whitespace && !strip_comments => {
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
                if !defines.contains_key(&ifid) && !is_predefined_text_macro(&ifid) {
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
                    } else if defines.contains_key(&elsifid) || is_predefined_text_macro(&ifid) {
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

                if !is_predefined_text_macro(id.as_str()) {
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
                }

                // Keep TextMacroDefinition after preprocess_inner().
                let locate: Locate = x.try_into().unwrap();
                let range = Range::new(locate.offset, locate.offset + locate.len);
                ret.push(locate.str(&s), Some((path.as_ref(), range)));
            }
            NodeEvent::Enter(RefNode::IncludeCompilerDirective(x)) if !ignore_include => {
                skip_nodes.push(x.into());
                skip = true;

                let locate: Locate = x.try_into().unwrap();
                last_include_line = Some(locate.line);

                // IEEE1800-2017 Clause 22.4, page 675
                // Only white space or a comment may appear on the same line as
                // the `include compiler directive.
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

                // IEEE1800-2017 Clause 22.4, page 675
                // The filename can be enclosed in either quotes or angle brackets,
                // which affects how a tool searches for the file, as follows:
                // - When the filename is enclosed in double quotes ("filename"), for
                //   a relative path the compiler’s current working directory, and
                //   optionally user-specified locations are searched.
                // - When the filename is enclosed in angle brackets (<filename>), then
                //   only an implementationdependent location containing files defined
                //   by the language standard is searched. Relative path names are
                //   interpreted relative to that location
                //
                // In this implementation, filenames enclosed in angle brackets are
                // treated equivalently to those enclosed in double quotes.
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
                    preprocess_inner(
                        path,
                        &defines,
                        include_paths,
                        strip_comments,
                        false, // ignore_include
                        include_depth + 1).map_err(
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

                // Push the trailing whitespace attached to either
                // TextMacroIdentifier or Option<Paren<ListOfActualArguments>>.
                let (ref _symbol, ref id, ref args) = x.nodes;
                match args {
                    Some(p) => {
                        // Arguments given to macro in parentheses.
                        let (ref _opening, ref _args, ref closing) = p.nodes;
                        for x in closing {
                            match x {
                                RefNode::WhiteSpace(x) => {
                                    let locate: Locate = x.try_into().unwrap();
                                    let range = Range::new(locate.offset, locate.offset + locate.len);
                                    ret.push(locate.str(&s), Some((path.as_ref(), range)));
                                }
                                _ => {
                                }
                            }
                        }
                    }
                    None => {
                        // No arguments given to macro.
                        for x in id {
                            match x {
                                RefNode::WhiteSpace(x) => {
                                    let locate: Locate = x.try_into().unwrap();
                                    let range = Range::new(locate.offset, locate.offset + locate.len);
                                    ret.push(locate.str(&s), Some((path.as_ref(), range)));
                                }
                                _ => {}
                            }
                        }
                    }
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

fn is_predefined_text_macro(s: &str) -> bool {
    match s {
        "__LINE__" | "__FILE__" => {
            true
        }
        _ => {
            false
        }
    }
}

fn split_text(s: &str) -> Vec<String> {
    let mut is_string = false;
    let mut is_ident = false;
    let mut is_ident_prev;
    let mut x = String::from("");
    let mut ret = vec![];

    // IEEE1800-2017 Clause 22.5.1, page 676
    // If a one-line comment (that is, a comment specified with the
    // characters //) is included in the text, then the comment shall not
    // become part of the substituted text.
    let mut is_comment = false;

    // IEEE1800-2017 Clause 22.5.1, page 680
    // An `" overrides the usual lexical meaning of " and indicates that the
    // expansion shall include the quotation mark, substitution of actual
    // arguments, and expansions of embedded macros.
    // This allows string literals to be constructed from macro arguments.
    let mut is_backquote_prev = false;

    let mut is_leading_whitespace = true;
    let mut is_backslash_prev = false;

    let mut iter = s.chars().peekable();
    while let Some(c) = iter.next() {

        // IEEE1800-2017 Clause 22.5.1, page 676, Syntax 22-2.
        // Ignore whitespace immediately after text_macro_name.
        if is_leading_whitespace {
            if c != '\\' && !c.is_ascii_whitespace() {
                // Non-whitespace character, move onto main loop.
                is_leading_whitespace = false;
            } else if is_backslash_prev && c == '\n' {
                // Drop the \n from leading continuation, then move onto main loop.
                is_leading_whitespace = false;
                continue;
            } else {
                // Still in leading whitespace or possible continuation.
                // Detect possible continuation, then try next character.
                is_backslash_prev = c == '\\';
                continue;
            }
        }

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
                            .replace("``", "")          // Argument substitution.
                            .replace("`\\`\"", "\\\"")  // Escaped backslash.
                            .replace("`\"", "\"")       // Escaped quote.
                            .replace("\\\n", "\n")      // Line continuation (Unix).
                            .replace("\\\r\n", "\r\n")  // Line continuation (Windows).
                            .replace("\\\r", "\r"),     // Line continuation (old Mac).
                    );
                }
            }

            if let Some(paren) = paren {
                replaced.push_str(&paren);
            }

            let (replaced, new_defines) = preprocess_str(
                &replaced,
                path.as_ref(),
                &defines,
                include_paths,
                false,
                strip_comments,
                resolve_depth,
                0, // include_depth
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

    fn testfile_path(s: &str) -> String {
        format!(
            "{}/testcases/{}",
            env::var("CARGO_MANIFEST_DIR").unwrap(),
            s
        )
    }

    fn testfile_contents(s: &str) -> String {
        let path: String = testfile_path(s);

        let file = File::open(path).unwrap();
        let mut buf_reader = BufReader::new(file);
        let mut contents = String::new();
        buf_reader.read_to_string(&mut contents).unwrap();

        contents
    }

    // Most tests are called with the same arguments, so this is a convenience.
    fn preprocess_usualargs(s: &str) -> Result<(PreprocessedText, Defines), Error> {
        let include_paths = [testfile_path("")];
        preprocess(
            testfile_path(s),   // path
            &HashMap::new(),    // pre_defines
            &include_paths,     // include_paths
            false,              // strip_comments
            false,              // ignore_include
        )
    }

    #[test]
    fn escaped_identifier() { // {{{
        let (ret, _) = preprocess_usualargs("escaped_identifier.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/escaped_identifier.sv")
        );
    } // }}}

    #[test]
    #[allow(non_snake_case)]
    fn IEEE18002017_keywords_if2_13642005() { // {{{
        let (ret, _) = preprocess_usualargs("IEEE18002017_keywords_if2_13642005.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/IEEE18002017_keywords_if2_13642005.sv")
        );
    } // }}}

    #[test]
    #[allow(non_snake_case)]
    fn IEEE18002017_keywords_m2_13642001() { // {{{
        let (ret, _) = preprocess_usualargs("IEEE18002017_keywords_m2_13642001.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/IEEE18002017_keywords_m2_13642001.sv")
        );
    } // }}}

    #[test]
    #[allow(non_snake_case)]
    fn IEEE18002017_keywords_m2_18002005() { // {{{
        let (ret, _) = preprocess_usualargs("IEEE18002017_keywords_m2_18002005.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/IEEE18002017_keywords_m2_18002005.sv")
        );
    } // }}}

    #[test]
    #[allow(non_snake_case)]
    fn IEEE18002017_macro_argument_expansion() { // {{{
        let (ret, _) = preprocess_usualargs("IEEE18002017_macro_argument_expansion.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/IEEE18002017_macro_argument_expansion.sv")
        );
    } // }}}

    #[test]
    #[allow(non_snake_case)]
    fn IEEE18002017_macro_delimit_tokens() { // {{{
        let (ret, _) = preprocess_usualargs("IEEE18002017_macro_delimit_tokens.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/IEEE18002017_macro_delimit_tokens.sv")
        );
    } // }}}

    #[test]
    #[allow(non_snake_case)]
    fn IEEE18002017_macro_mix_quotes() { // {{{
        let (ret, _) = preprocess_usualargs("IEEE18002017_macro_mix_quotes.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/IEEE18002017_macro_mix_quotes.sv")
        );
    } // }}}

    #[test]
    #[allow(non_snake_case)]
    fn IEEE18002017_macro_noexpand_string() { // {{{
        let (ret, _) = preprocess_usualargs("IEEE18002017_macro_noexpand_string.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/IEEE18002017_macro_noexpand_string.sv")
        );
    } // }}}

    #[test]
    #[allow(non_snake_case)]
    fn IEEE18002017_macro_with_defaults() { // {{{
        let (ret, _) = preprocess_usualargs("IEEE18002017_macro_with_defaults.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/IEEE18002017_macro_with_defaults.sv")
        );
    } // }}}

    #[test]
    #[allow(non_snake_case)]
    fn IEEE18002017_macro_without_defaults() { // {{{
        let (ret, _) = preprocess_usualargs("IEEE18002017_macro_without_defaults.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/IEEE18002017_macro_without_defaults.sv")
        );
    } // }}}

    #[test]
    fn celldefine() { // {{{
        let (ret, _) = preprocess_usualargs("celldefine.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("celldefine.sv")
        );
    } // }}}

    #[test]
    fn default_nettype() { // {{{
        let (ret, _) = preprocess_usualargs("default_nettype.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("default_nettype.sv")
        );
    } // }}}

    #[test]
    fn ifdef_nested() { // {{{
        let (ret, _) = preprocess_usualargs("ifdef_nested.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/ifdef_nested.sv")
        );
    } // }}}

    #[test]
    fn ifdef_predefined() { // {{{
        let mut defines = HashMap::new();
        defines.insert(String::from("behavioral"), None);
        let (ret, _) = preprocess(
            testfile_path("ifdef_predefined.sv"),
            &defines,
            &[] as &[String],
            false, // strip_comments
            false, // ignore_include
        )
        .unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/ifdef_predefined.sv")
        )
    } // }}}

    #[test]
    fn ifdef_undefined() { // {{{
        let (ret, _) = preprocess_usualargs("ifdef_undefined.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/ifdef_undefined.sv")
        );
        assert_eq!(
            ret.origin(10).unwrap().0,
            &PathBuf::from(testfile_path("ifdef_undefined.sv"))
        );
        assert_eq!(ret.origin(10).unwrap().1, 10);
        assert_eq!(ret.origin(50).unwrap().1, 98);
        assert_eq!(ret.origin(70).unwrap().1, 124);
    } // }}}

    #[test]
    fn ifndef_undefined() { // {{{
        let (ret, _) = preprocess_usualargs("ifndef_undefined.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/ifndef_undefined.sv")
        );
    } // }}}

    #[test]
    fn include_ignore() { // {{{
        let include_paths = [testfile_path("")];
        let (ret, _) = preprocess(
            testfile_path("include_ignore.sv"),
            &HashMap::new(),
            &include_paths,
            false, // strip_comments
            true, // ignore_include
        )
        .unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/include_ignore.sv")
        );
    } // }}}

    #[test]
    fn include_noindent() { // {{{
        let (ret, _) = preprocess_usualargs("include_noindent.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/include_noindent.sv")
        );

        // 11th char of returned text is '_' in the module identifier
        // "and_op", and originates from the parent file.
        // Characters are zero-indexed.
        let n = 10;
        assert_eq!(
            ret.origin(n).unwrap(),
            (&PathBuf::from(testfile_path("include_noindent.sv")), n)
        );
        assert_eq!(ret.text().chars().nth(n).unwrap(), '_');

        // 51st char of returned text is 'd' in the primitive identifier
        // "and", and originates from the child file at character index 72.
        let n = 50;
        assert_eq!(
            ret.origin(n).unwrap(),
            (&PathBuf::from(testfile_path("included.svh")), 73)
        );
        assert_eq!(ret.text().chars().nth(n).unwrap(), 'd');

        // 71st char of returned text is 'o' in the keword "endmodule", and
        // originates from the parent file.
        let n = 70;
        assert_eq!(
            ret.origin(n).unwrap(),
            (&PathBuf::from(testfile_path("include_noindent.sv")), 53)
        );
        assert_eq!(ret.text().chars().nth(n).unwrap(), 'o');
    } // }}}

    #[test]
    fn include_quoted_a() { // {{{
        let ret = preprocess_usualargs("include_quoted_a.sv");
        assert_eq!(format!("{:?}", ret), "Err(Include { source: File { source: Os { code: 2, kind: NotFound, message: \"No such file or directory\" }, path: \"`PATH\" } })");
    } // }}}

    #[test]
    fn include_quoted_b() { // {{{
        let ret = preprocess_usualargs("include_quoted_b.sv");
        assert_eq!(format!("{:?}", ret), "Err(Include { source: File { source: Os { code: 2, kind: NotFound, message: \"No such file or directory\" }, path: \"`PATH\" } })");
    } // }}}

    #[test]
    fn include_quoted_c() { // {{{
        let (ret, _) = preprocess_usualargs("include_quoted_c.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/include_quoted_c.sv")
        );
    } // }}}

    #[test]
    fn include_quoted_d() { // {{{
        let (ret, _) = preprocess_usualargs("include_quoted_d.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/include_quoted_d.sv")
        );
    } // }}}

    #[test]
    fn include_recursive() { // {{{
        let ret = preprocess_usualargs("include_recursive.svh");
        let expected = format!(
            "Err({}ExceedRecursiveLimit{})",
            "Include { source: ".repeat(RECURSIVE_LIMIT+1),
            " }".repeat(RECURSIVE_LIMIT+1),
        );
        assert_eq!(format!("{:?}", ret), expected);
    } // }}}

    #[test]
    fn include_sameline_comment() { // {{{
        let (ret, _) = preprocess_usualargs("include_sameline_comment.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/include_sameline_comment.sv")
        );
        assert_eq!(
            ret.origin(10).unwrap().0,
            &PathBuf::from(testfile_path("include_sameline_comment.sv"))
        );
        assert_eq!(ret.origin(10).unwrap().1, 10);
        assert_eq!(
            ret.origin(50).unwrap().0,
            &PathBuf::from(testfile_path("included.svh"))
        );
        assert_eq!(ret.origin(50).unwrap().1, 73);
        assert_eq!(
            ret.origin(70).unwrap().0,
            &PathBuf::from(testfile_path("include_sameline_comment.sv"))
        );
        assert_eq!(ret.origin(70).unwrap().1, 53);
    } // }}}

    #[test]
    fn include_sameline_include() { // {{{
        let ret = preprocess_usualargs("include_sameline_include.sv");
        assert_eq!(format!("{:?}", ret), "Err(IncludeLine)");
    } // }}}

    #[test]
    fn include_sameline_keyword() { // {{{
        let ret = preprocess_usualargs("include_sameline_keyword.sv");
        assert_eq!(format!("{:?}", ret), "Err(IncludeLine)");
    } // }}}

    #[test]
    fn include_withindent() { // {{{
        let (ret, _) = preprocess_usualargs("include_withindent.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/include_withindent.sv")
        );

        // 11th char of returned text is '_' in the module identifier
        // "and_op", and originates from the parent file.
        // Characters are zero-indexed.
        let n = 10;
        assert_eq!(
            ret.origin(n).unwrap(),
            (&PathBuf::from(testfile_path("include_withindent.sv")), n)
        );
        assert_eq!(ret.text().chars().nth(n).unwrap(), '_');

        // 59th char of returned text is 'n' in the primitive identifier
        // "and", and originates from the child file at character index 72.
        let n = 58;
        assert_eq!(
            ret.origin(n).unwrap(),
            (&PathBuf::from(testfile_path("included.svh")), 72)
        );
        assert_eq!(ret.text().chars().nth(n).unwrap(), 'n');

        // 80th char of returned text is 'o' in the keyword "endmodule", and
        // originates from the parent file.
        let n = 79;
        assert_eq!(
            ret.origin(n).unwrap(),
            (&PathBuf::from(testfile_path("include_withindent.sv")), 62)
        );
        assert_eq!(ret.text().chars().nth(n).unwrap(), 'o');
    } // }}}

    #[test]
    fn keywords() { // {{{
        let (ret, _) = preprocess_usualargs("keywords.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("keywords.sv")
        );
    } // }}}

    #[test]
    fn line() { // {{{
        let (ret, _) = preprocess_usualargs("line.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("line.sv")
        );
    } // }}}

    #[test]
    fn macro_arguments() { // {{{
        let (ret, _) = preprocess_usualargs("macro_arguments.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/macro_arguments.sv")
        );
    } // }}}

    #[test]
    fn macro_basic() { // {{{
        let (ret, _) = preprocess_usualargs("macro_basic.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/macro_basic.sv")
        );
    } // }}}

    #[test]
    fn macro_comment() { // {{{
        let (ret, _) = preprocess_usualargs("macro_comment.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/macro_comment.sv")
        );
    } // }}}

    #[test]
    #[ignore = "Exposes unfixed PP parser bug."]
    fn macro_comment_embedded() { // {{{
        let (ret, _) = preprocess_usualargs("macro_comment_embedded.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/macro_comment_embedded.sv")
        );
    } // }}}

    #[test]
    fn macro_delimiters() { // {{{
        let (ret, _) = preprocess_usualargs("macro_delimiters.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/macro_delimiters.sv")
        );
    } // }}}

    #[test]
    #[allow(non_snake_case)]
    fn macro_FILE() { // {{{
        let (ret, _) = preprocess_usualargs("macro_FILE.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/macro_FILE.sv")
        );
    } // }}}

    #[test]
    fn macro_identifier() { // {{{
        let (ret, _) = preprocess_usualargs("macro_identifier.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/macro_identifier.sv")
        );
    } // }}}

    #[test]
    #[allow(non_snake_case)]
    fn macro_LINE() { // {{{
        let (ret, _) = preprocess_usualargs("macro_LINE.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/macro_LINE.sv")
        );
    } // }}}

    #[test]
    fn macro_multiline_comment() { // {{{
        let (ret, _) = preprocess_usualargs("macro_multiline_comment.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/macro_multiline_comment.sv")
        );
    } // }}}

    #[test]
    fn macro_recursion_direct() { // {{{
        let ret = preprocess_usualargs("macro_recursion_direct.sv");
        assert_eq!(format!("{:?}", ret), "Err(ExceedRecursiveLimit)");
    } // }}}

    #[test]
    fn macro_recursion_indirect() { // {{{
        let ret = preprocess_usualargs("macro_recursion_indirect.sv");
        assert_eq!(format!("{:?}", ret), "Err(ExceedRecursiveLimit)");
    } // }}}

    #[test]
    fn pragma() { // {{{
        let (ret, _) = preprocess_usualargs("pragma.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("pragma.sv")
        );
    } // }}}

    #[test]
    fn resetall() { // {{{
        let (ret, _) = preprocess_usualargs("resetall.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("resetall.sv")
        );
    } // }}}

    #[test]
    fn timescale() { // {{{
        let (ret, _) = preprocess_usualargs("timescale.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("timescale.sv")
        );
    } // }}}

    #[test]
    fn unconnected_drive() { // {{{
        let (ret, _) = preprocess_usualargs("unconnected_drive.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("unconnected_drive.sv")
        );
    } // }}}

    #[test]
    fn undef() { // {{{
        let (ret, _) = preprocess_usualargs("undef.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/undef.sv")
        );
    } // }}}

    #[test]
    fn undefineall() { // {{{
        let (ret, _) = preprocess_usualargs("undefineall.sv").unwrap();
        assert_eq!(
            ret.text(),
            testfile_contents("expected/undefineall.sv")
        );
    } // }}}
}
