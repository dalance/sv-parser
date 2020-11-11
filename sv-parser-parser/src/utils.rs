use crate::*;

// -----------------------------------------------------------------------------

pub(crate) fn ws<'a, O, F>(
    mut f: F,
) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, (O, Vec<WhiteSpace>)>
where
    F: FnMut(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (s, x) = f(s)?;
        let (s, y) = many0(white_space)(s)?;
        Ok((s, (x, y)))
    }
}

pub(crate) fn no_ws<'a, O, F>(
    mut f: F,
) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, (O, Vec<WhiteSpace>)>
where
    F: FnMut(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (s, x) = f(s)?;
        Ok((s, (x, vec![])))
    }
}

#[cfg(not(feature = "trace"))]
pub(crate) fn symbol<'a>(t: &'a str) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, Symbol> {
    move |s: Span<'a>| {
        let (s, x) = map(ws(map(tag(t), into_locate)), |x| Symbol { nodes: x })(s)?;
        Ok((s, x))
    }
}

#[cfg(feature = "trace")]
pub(crate) fn symbol<'a>(t: &'a str) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, Symbol> {
    move |s: Span<'a>| {
        let (depth, s) = nom_tracable::forward_trace(s, &format!("symbol(\"{}\")", t));
        let body = || {
            let (s, x) = map(ws(map(tag(t), into_locate)), |x| Symbol { nodes: x })(s)?;
            Ok((s, x))
        };
        let ret = body();
        nom_tracable::backward_trace(ret, &format!("symbol(\"{}\")", t), depth)
    }
}

#[cfg(not(feature = "trace"))]
pub(crate) fn symbol_exact<'a>(t: &'a str) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, Symbol> {
    move |s: Span<'a>| {
        let (s, x) = map(no_ws(map(tag(t), into_locate)), |x| Symbol { nodes: x })(s)?;
        Ok((s, x))
    }
}

#[cfg(feature = "trace")]
pub(crate) fn symbol_exact<'a>(t: &'a str) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, Symbol> {
    move |s: Span<'a>| {
        let (depth, s) = nom_tracable::forward_trace(s, &format!("symbol(\"{}\")", t));
        let body = || {
            let (s, x) = map(no_ws(map(tag(t), into_locate)), |x| Symbol { nodes: x })(s)?;
            Ok((s, x))
        };
        let ret = body();
        nom_tracable::backward_trace(ret, &format!("symbol(\"{}\")", t), depth)
    }
}

#[cfg(not(feature = "trace"))]
pub(crate) fn keyword<'a>(t: &'a str) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, Keyword> {
    move |s: Span<'a>| {
        let (s, x) = map(
            ws(alt((
                all_consuming(map(tag(t), into_locate)),
                terminated(map(tag(t), into_locate), peek(none_of(AZ09_))),
            ))),
            |x| Keyword { nodes: x },
        )(s)?;
        Ok((s, x))
    }
}

#[cfg(feature = "trace")]
pub(crate) fn keyword<'a>(t: &'a str) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, Keyword> {
    move |s: Span<'a>| {
        let (depth, s) = nom_tracable::forward_trace(s, &format!("keyword(\"{}\")", t));
        let body = || {
            let (s, x) = map(
                ws(alt((
                    all_consuming(map(tag(t), into_locate)),
                    terminated(map(tag(t), into_locate), peek(none_of(AZ09_))),
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
pub(crate) fn paren<'a, O, F>(mut f: F) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, Paren<O>>
where
    F: FnMut(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (s, a) = symbol("(")(s)?;
        let (s, b) = f(s)?;
        let (s, c) = symbol(")")(s)?;
        Ok((s, Paren { nodes: (a, b, c) }))
    }
}

#[cfg(feature = "trace")]
pub(crate) fn paren<'a, O, F>(mut f: F) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, Paren<O>>
where
    F: FnMut(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (depth, s) = nom_tracable::forward_trace(s, "paren");
        let mut body = || {
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
pub(crate) fn paren_exact<'a, O, F>(mut f: F) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, Paren<O>>
where
    F: FnMut(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (s, a) = symbol("(")(s)?;
        let (s, b) = f(s)?;
        let (s, c) = symbol_exact(")")(s)?;
        Ok((s, Paren { nodes: (a, b, c) }))
    }
}

#[cfg(feature = "trace")]
pub(crate) fn paren_exact<'a, O, F>(mut f: F) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, Paren<O>>
where
    F: FnMut(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (depth, s) = nom_tracable::forward_trace(s, "paren");
        let mut body = || {
            let (s, a) = symbol("(")(s)?;
            let (s, b) = f(s)?;
            let (s, c) = symbol_exact(")")(s)?;
            Ok((s, Paren { nodes: (a, b, c) }))
        };
        let ret = body();
        nom_tracable::backward_trace(ret, "paren", depth)
    }
}

#[cfg(not(feature = "trace"))]
pub(crate) fn bracket<'a, O, F>(mut f: F) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, Bracket<O>>
where
    F: FnMut(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (s, a) = symbol("[")(s)?;
        let (s, b) = f(s)?;
        let (s, c) = symbol("]")(s)?;
        Ok((s, Bracket { nodes: (a, b, c) }))
    }
}

#[cfg(feature = "trace")]
pub(crate) fn bracket<'a, O, F>(mut f: F) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, Bracket<O>>
where
    F: FnMut(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (depth, s) = nom_tracable::forward_trace(s, "bracket");
        let mut body = || {
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
pub(crate) fn brace<'a, O, F>(mut f: F) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, Brace<O>>
where
    F: FnMut(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (s, a) = symbol("{")(s)?;
        let (s, b) = f(s)?;
        let (s, c) = symbol("}")(s)?;
        Ok((s, Brace { nodes: (a, b, c) }))
    }
}

#[cfg(feature = "trace")]
pub(crate) fn brace<'a, O, F>(mut f: F) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, Brace<O>>
where
    F: FnMut(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (depth, s) = nom_tracable::forward_trace(s, "brace");
        let mut body = || {
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
    mut f: F,
) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, ApostropheBrace<O>>
where
    F: FnMut(Span<'a>) -> IResult<Span<'a>, O>,
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
    mut f: F,
) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, ApostropheBrace<O>>
where
    F: FnMut(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (depth, s) = nom_tracable::forward_trace(s, "apostrophe_brace");
        let mut body = || {
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
    mut f: F,
    mut g: G,
) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, List<O1, O2>>
where
    F: FnMut(Span<'a>) -> IResult<Span<'a>, O1>,
    G: FnMut(Span<'a>) -> IResult<Span<'a>, O2>,
{
    move |s: Span<'a>| {
        let (s, a) = g(s)?;
        let mut s = s;
        let mut ret = Vec::new();
        while let Ok((t, b)) = f(s) {
            if let Ok((u, c)) = g(t) {
                s = u;
                ret.push((b, c));
            } else {
                break;
            }
        }
        Ok((s, List { nodes: (a, ret) }))
    }
}

pub(crate) fn triple<'a, O1, O2, O3, F, G, H>(
    mut f: F,
    mut g: G,
    mut h: H,
) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, (O1, O2, O3)>
where
    F: FnMut(Span<'a>) -> IResult<Span<'a>, O1>,
    G: FnMut(Span<'a>) -> IResult<Span<'a>, O2>,
    H: FnMut(Span<'a>) -> IResult<Span<'a>, O3>,
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
#[packrat_parser]
pub(crate) fn white_space(s: Span) -> IResult<Span, WhiteSpace> {
    if in_directive() {
        alt((
            map(multispace1, |x: Span| {
                WhiteSpace::Space(Box::new(into_locate(x)))
            }),
            map(preceded(peek(char('/')), comment), |x| {
                WhiteSpace::Comment(Box::new(x))
            }),
        ))(s)
    } else {
        alt((
            map(multispace1, |x: Span| {
                WhiteSpace::Space(Box::new(into_locate(x)))
            }),
            map(preceded(peek(char('/')), comment), |x| {
                WhiteSpace::Comment(Box::new(x))
            }),
            map(
                preceded(peek(char('`')), compiler_directive_without_resetall),
                |x| WhiteSpace::CompilerDirective(Box::new(x)),
            ),
        ))(s)
    }
}

thread_local!(
    static IN_DIRECTIVE: core::cell::RefCell<Vec<()>> = {
        core::cell::RefCell::new(Vec::new())
    }
);

pub(crate) fn in_directive() -> bool {
    IN_DIRECTIVE.with(|x| x.borrow().last().is_some())
}

pub(crate) fn begin_directive() {
    IN_DIRECTIVE.with(|x| x.borrow_mut().push(()));
}

pub(crate) fn end_directive() {
    IN_DIRECTIVE.with(|x| x.borrow_mut().pop());
}

// -----------------------------------------------------------------------------

#[derive(Clone, Copy)]
pub(crate) enum VersionSpecifier {
    Ieee1364_1995,
    Ieee1364_2001,
    Ieee1364_2001Noconfig,
    Ieee1364_2005,
    Ieee1800_2005,
    Ieee1800_2009,
    Ieee1800_2012,
    Ieee1800_2017,
    Directive,
}

thread_local!(
    static CURRENT_VERSION: core::cell::RefCell<Vec<VersionSpecifier>> = {
        core::cell::RefCell::new(Vec::new())
    }
);

pub(crate) fn begin_keywords(version: &str) {
    CURRENT_VERSION.with(|current_version| match version {
        "1364-1995" => current_version
            .borrow_mut()
            .push(VersionSpecifier::Ieee1364_1995),
        "1364-2001" => current_version
            .borrow_mut()
            .push(VersionSpecifier::Ieee1364_2001),
        "1364-2001-noconfig" => current_version
            .borrow_mut()
            .push(VersionSpecifier::Ieee1364_2001Noconfig),
        "1364-2005" => current_version
            .borrow_mut()
            .push(VersionSpecifier::Ieee1364_2005),
        "1800-2005" => current_version
            .borrow_mut()
            .push(VersionSpecifier::Ieee1800_2005),
        "1800-2009" => current_version
            .borrow_mut()
            .push(VersionSpecifier::Ieee1800_2009),
        "1800-2012" => current_version
            .borrow_mut()
            .push(VersionSpecifier::Ieee1800_2012),
        "1800-2017" => current_version
            .borrow_mut()
            .push(VersionSpecifier::Ieee1800_2017),
        "directive" => current_version
            .borrow_mut()
            .push(VersionSpecifier::Directive),
        _ => (),
    });
}

pub(crate) fn end_keywords() {
    CURRENT_VERSION.with(|current_version| {
        current_version.borrow_mut().pop();
    });
}

pub(crate) fn current_version() -> Option<VersionSpecifier> {
    CURRENT_VERSION.with(|current_version| match current_version.borrow().last() {
        Some(x) => Some(*x),
        None => None,
    })
}

// -----------------------------------------------------------------------------

pub(crate) fn concat<'a>(a: Span<'a>, b: Span<'a>) -> Option<Span<'a>> {
    let c = unsafe { str_concat::concat(a.fragment(), b.fragment()) };
    if let Ok(c) = c {
        let ret = unsafe {
            Span::new_from_raw_offset(a.location_offset(), a.location_line(), c, a.extra)
        };
        Some(ret)
    } else {
        None
    }
}

pub(crate) fn is_keyword(s: &Span) -> bool {
    let keywords = match current_version() {
        Some(VersionSpecifier::Ieee1364_1995) => KEYWORDS_1364_1995,
        Some(VersionSpecifier::Ieee1364_2001) => KEYWORDS_1364_2001,
        Some(VersionSpecifier::Ieee1364_2001Noconfig) => KEYWORDS_1364_2001_NOCONFIG,
        Some(VersionSpecifier::Ieee1364_2005) => KEYWORDS_1364_2005,
        Some(VersionSpecifier::Ieee1800_2005) => KEYWORDS_1800_2005,
        Some(VersionSpecifier::Ieee1800_2009) => KEYWORDS_1800_2009,
        Some(VersionSpecifier::Ieee1800_2012) => KEYWORDS_1800_2012,
        Some(VersionSpecifier::Ieee1800_2017) => KEYWORDS_1800_2017,
        Some(VersionSpecifier::Directive) => KEYWORDS_DIRECTIVE,
        None => KEYWORDS_1800_2017,
    };
    for k in keywords {
        if s.fragment() == k {
            return true;
        }
    }
    false
}

pub(crate) fn into_locate(s: Span) -> Locate {
    Locate {
        offset: s.location_offset(),
        line: s.location_line(),
        len: s.fragment().len(),
    }
}
