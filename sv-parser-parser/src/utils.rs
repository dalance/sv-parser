use crate::*;

// -----------------------------------------------------------------------------

const KEYWORDS: &[&str] = &[
    "accept_on",
    "alias",
    "always",
    "always_comb",
    "always_ff",
    "always_latch",
    "and",
    "assert",
    "assign",
    "assume",
    "automatic",
    "before",
    "begin",
    "bind",
    "bins",
    "binsof",
    "bit",
    "break",
    "buf",
    "bufif0",
    "bufif1",
    "byte",
    "case",
    "casex",
    "casez",
    "cell",
    "chandle",
    "checker",
    "class",
    "clocking",
    "cmos",
    "config",
    "const",
    "constraint",
    "context",
    "continue",
    "cover",
    "covergroup",
    "coverpoint",
    "cross",
    "deassign",
    "default",
    "defparam",
    "design",
    "disable",
    "dist",
    "do",
    "edge",
    "else",
    "end",
    "endcase",
    "endchecker",
    "endclass",
    "endclocking",
    "endconfig",
    "endfunction",
    "endgenerate",
    "endgroup",
    "endinterface",
    "endmodule",
    "endpackage",
    "endprimitive",
    "endprogram",
    "endproperty",
    "endspecify",
    "endsequence",
    "endtable",
    "endtask",
    "enum",
    "event",
    "eventually",
    "expect",
    "export",
    "extends",
    "extern",
    "final",
    "first_match",
    "for",
    "force",
    "foreach",
    "forever",
    "fork",
    "forkjoin",
    "function",
    "generate",
    "genvar",
    "global",
    "highz0",
    "highz1",
    "if",
    "iff",
    "ifnone",
    "ignore_bins",
    "illegal_bins",
    "implements",
    "implies",
    "import",
    "incdir",
    "include",
    "initial",
    "inout",
    "input",
    "inside",
    "instance",
    "int",
    "integer",
    "interconnect",
    "interface",
    "intersect",
    "join",
    "join_any",
    "join_none",
    "large",
    "let",
    "liblist",
    "library",
    "local",
    "localparam",
    "logic",
    "longint",
    "macromodule",
    "matches",
    "medium",
    "modport",
    "module",
    "nand",
    "negedge",
    "nettype",
    "new",
    "nexttime",
    "nmos",
    "nor",
    "noshowcancelled",
    "not",
    "notif0",
    "notif1",
    "null",
    "or",
    "output",
    "package",
    "packed",
    "parameter",
    "pmos",
    "posedge",
    "primitive",
    "priority",
    "program",
    "property",
    "protected",
    "pull0",
    "pull1",
    "pulldown",
    "pullup",
    "pulsestyle_ondetect",
    "pulsestyle_onevent",
    "pure",
    "rand",
    "randc",
    "randcase",
    "randsequence",
    "rcmos",
    "real",
    "realtime",
    "ref",
    "reg",
    "reject_on",
    "release",
    "repeat",
    "restrict",
    "return",
    "rnmos",
    "rpmos",
    "rtran",
    "rtranif0",
    "rtranif1",
    "s_always",
    "s_eventually",
    "s_nexttime",
    "s_until",
    "s_until_with",
    "scalared",
    "sequence",
    "shortint",
    "shortreal",
    "showcancelled",
    "signed",
    "small",
    "soft",
    "solve",
    "specify",
    "specparam",
    "static",
    "string",
    "strong",
    "strong0",
    "strong1",
    "struct",
    "super",
    "supply0",
    "supply1",
    "sync_accept_on",
    "sync_reject_on",
    "table",
    "tagged",
    "task",
    "this",
    "throughout",
    "time",
    "timeprecision",
    "timeunit",
    "tran",
    "tranif0",
    "tranif1",
    "tri",
    "tri0",
    "tri1",
    "triand",
    "trior",
    "trireg",
    "type",
    "typedef",
    "union",
    "unique",
    "unique0",
    "unsigned",
    "until",
    "until_with",
    "untyped",
    "use",
    "uwire",
    "var",
    "vectored",
    "virtual",
    "void",
    "wait",
    "wait_order",
    "wand",
    "weak",
    "weak0",
    "weak1",
    "while",
    "wildcard",
    "wire",
    "with",
    "within",
    "wor",
    "xnor",
    "xor",
];

// -----------------------------------------------------------------------------

pub(crate) fn ws<'a, O, F>(f: F) -> impl Fn(Span<'a>) -> IResult<Span<'a>, (O, Vec<WhiteSpace>)>
where
    F: Fn(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (s, x) = f(s)?;
        let (s, y) = many0(white_space)(s)?;
        Ok((s, (x, y)))
    }
}

#[cfg(not(feature = "trace"))]
pub(crate) fn symbol<'a>(t: &'a str) -> impl Fn(Span<'a>) -> IResult<Span<'a>, Symbol> {
    move |s: Span<'a>| {
        let (s, x) = map(ws(map(tag(t.clone()), |x: Span| into_locate(x))), |x| {
            Symbol { nodes: x }
        })(s)?;
        Ok((s, x))
    }
}

#[cfg(feature = "trace")]
pub(crate) fn symbol<'a>(t: &'a str) -> impl Fn(Span<'a>) -> IResult<Span<'a>, Symbol> {
    move |s: Span<'a>| {
        let (depth, s) = nom_tracable::forward_trace(s, &format!("symbol(\"{}\")", t));
        let body = || {
            let (s, x) = map(ws(map(tag(t.clone()), |x: Span| into_locate(x))), |x| {
                Symbol { nodes: x }
            })(s)?;
            Ok((s, x))
        };
        let ret = body();
        nom_tracable::backward_trace(ret, &format!("symbol(\"{}\")", t), depth)
    }
}

#[cfg(not(feature = "trace"))]
pub(crate) fn keyword<'a>(t: &'a str) -> impl Fn(Span<'a>) -> IResult<Span<'a>, Keyword> {
    move |s: Span<'a>| {
        let (s, x) = map(
            ws(alt((
                all_consuming(map(tag(t.clone()), |x: Span| into_locate(x))),
                terminated(
                    map(tag(t.clone()), |x: Span| into_locate(x)),
                    peek(none_of(AZ09_)),
                ),
            ))),
            |x| Keyword { nodes: x },
        )(s)?;
        Ok((s, x))
    }
}

#[cfg(feature = "trace")]
pub(crate) fn keyword<'a>(t: &'a str) -> impl Fn(Span<'a>) -> IResult<Span<'a>, Keyword> {
    move |s: Span<'a>| {
        let (depth, s) = nom_tracable::forward_trace(s, &format!("keyword(\"{}\")", t));
        let body = || {
            let (s, x) = map(
                ws(alt((
                    all_consuming(map(tag(t.clone()), |x: Span| into_locate(x))),
                    terminated(
                        map(tag(t.clone()), |x: Span| into_locate(x)),
                        peek(none_of(AZ09_)),
                    ),
                ))),
                |x| Keyword { nodes: x },
            )(s)?;
            Ok((s, x))
        };
        let ret = body();
        nom_tracable::backward_trace(ret, &format!("keyword(\"{}\")", t), depth)
    }
}

#[cfg(not(feature = "trace"))]
pub(crate) fn paren<'a, O, F>(f: F) -> impl Fn(Span<'a>) -> IResult<Span<'a>, Paren<O>>
where
    F: Fn(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (s, a) = symbol("(")(s)?;
        let (s, b) = f(s)?;
        let (s, c) = symbol(")")(s)?;
        Ok((s, Paren { nodes: (a, b, c) }))
    }
}

#[cfg(feature = "trace")]
pub(crate) fn paren<'a, O, F>(f: F) -> impl Fn(Span<'a>) -> IResult<Span<'a>, Paren<O>>
where
    F: Fn(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (depth, s) = nom_tracable::forward_trace(s, "paren");
        let body = || {
            let (s, a) = symbol("(")(s)?;
            let (s, b) = f(s)?;
            let (s, c) = symbol(")")(s)?;
            Ok((s, Paren { nodes: (a, b, c) }))
        };
        let ret = body();
        nom_tracable::backward_trace(ret, "paren", depth)
    }
}

#[cfg(not(feature = "trace"))]
pub(crate) fn bracket<'a, O, F>(f: F) -> impl Fn(Span<'a>) -> IResult<Span<'a>, Bracket<O>>
where
    F: Fn(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (s, a) = symbol("[")(s)?;
        let (s, b) = f(s)?;
        let (s, c) = symbol("]")(s)?;
        Ok((s, Bracket { nodes: (a, b, c) }))
    }
}

#[cfg(feature = "trace")]
pub(crate) fn bracket<'a, O, F>(f: F) -> impl Fn(Span<'a>) -> IResult<Span<'a>, Bracket<O>>
where
    F: Fn(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (depth, s) = nom_tracable::forward_trace(s, "bracket");
        let body = || {
            let (s, a) = symbol("[")(s)?;
            let (s, b) = f(s)?;
            let (s, c) = symbol("]")(s)?;
            Ok((s, Bracket { nodes: (a, b, c) }))
        };
        let ret = body();
        nom_tracable::backward_trace(ret, "bracket", depth)
    }
}

#[cfg(not(feature = "trace"))]
pub(crate) fn brace<'a, O, F>(f: F) -> impl Fn(Span<'a>) -> IResult<Span<'a>, Brace<O>>
where
    F: Fn(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (s, a) = symbol("{")(s)?;
        let (s, b) = f(s)?;
        let (s, c) = symbol("}")(s)?;
        Ok((s, Brace { nodes: (a, b, c) }))
    }
}

#[cfg(feature = "trace")]
pub(crate) fn brace<'a, O, F>(f: F) -> impl Fn(Span<'a>) -> IResult<Span<'a>, Brace<O>>
where
    F: Fn(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (depth, s) = nom_tracable::forward_trace(s, "brace");
        let body = || {
            let (s, a) = symbol("{")(s)?;
            let (s, b) = f(s)?;
            let (s, c) = symbol("}")(s)?;
            Ok((s, Brace { nodes: (a, b, c) }))
        };
        let ret = body();
        nom_tracable::backward_trace(ret, "brace", depth)
    }
}

#[cfg(not(feature = "trace"))]
pub(crate) fn apostrophe_brace<'a, O, F>(
    f: F,
) -> impl Fn(Span<'a>) -> IResult<Span<'a>, ApostropheBrace<O>>
where
    F: Fn(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (s, a) = symbol("'{")(s)?;
        let (s, b) = f(s)?;
        let (s, c) = symbol("}")(s)?;
        Ok((s, ApostropheBrace { nodes: (a, b, c) }))
    }
}

#[cfg(feature = "trace")]
pub(crate) fn apostrophe_brace<'a, O, F>(
    f: F,
) -> impl Fn(Span<'a>) -> IResult<Span<'a>, ApostropheBrace<O>>
where
    F: Fn(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (depth, s) = nom_tracable::forward_trace(s, "apostrophe_brace");
        let body = || {
            let (s, a) = symbol("'{")(s)?;
            let (s, b) = f(s)?;
            let (s, c) = symbol("}")(s)?;
            Ok((s, ApostropheBrace { nodes: (a, b, c) }))
        };
        let ret = body();
        nom_tracable::backward_trace(ret, "apostrophe_brace", depth)
    }
}

pub(crate) fn list<'a, O1, O2, F, G>(
    f: F,
    g: G,
) -> impl Fn(Span<'a>) -> IResult<Span<'a>, List<O1, O2>>
where
    F: Fn(Span<'a>) -> IResult<Span<'a>, O1>,
    G: Fn(Span<'a>) -> IResult<Span<'a>, O2>,
{
    move |s: Span<'a>| {
        let (s, a) = g(s)?;
        let mut s = s.clone();
        let mut ret = Vec::new();
        loop {
            if let Ok((t, b)) = f(s) {
                if let Ok((u, c)) = g(t) {
                    s = u;
                    ret.push((b, c));
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        Ok((s, List { nodes: (a, ret) }))
    }
}

pub(crate) fn triple<'a, O1, O2, O3, F, G, H>(
    f: F,
    g: G,
    h: H,
) -> impl Fn(Span<'a>) -> IResult<Span<'a>, (O1, O2, O3)>
where
    F: Fn(Span<'a>) -> IResult<Span<'a>, O1>,
    G: Fn(Span<'a>) -> IResult<Span<'a>, O2>,
    H: Fn(Span<'a>) -> IResult<Span<'a>, O3>,
{
    move |s: Span<'a>| {
        let (s, x) = f(s)?;
        let (s, y) = g(s)?;
        let (s, z) = h(s)?;
        Ok((s, (x, y, z)))
    }
}

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn white_space(s: Span) -> IResult<Span, WhiteSpace> {
    alt((
        map(multispace1, |x: Span| {
            WhiteSpace::Space(Box::new(into_locate(x)))
        }),
        map(comment, |x| WhiteSpace::Comment(Box::new(x))),
    ))(s)
}

// -----------------------------------------------------------------------------

pub(crate) fn concat<'a>(a: Span<'a>, b: Span<'a>) -> Option<Span<'a>> {
    let c = str_concat::concat(a.fragment, b.fragment);
    if let Ok(c) = c {
        Some(Span {
            offset: a.offset,
            line: a.line,
            fragment: c,
            extra: a.extra,
        })
    } else {
        None
    }
}

pub(crate) fn is_keyword(s: &Span) -> bool {
    for k in KEYWORDS {
        if &s.fragment == k {
            return true;
        }
    }
    false
}

pub(crate) fn into_locate(s: Span) -> Locate {
    Locate {
        offset: s.offset,
        line: s.line,
        len: s.fragment.len(),
    }
}
