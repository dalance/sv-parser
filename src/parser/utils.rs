use crate::parser::*;
use nom::branch::*;
use nom::bytes::complete::*;
use nom::character::complete::*;
use nom::combinator::*;
use nom::multi::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct Symbol<'a> {
    pub nodes: (Span<'a>, Vec<WhiteSpace<'a>>),
}

#[derive(Debug)]
pub enum WhiteSpace<'a> {
    Space(Span<'a>),
    Comment(Comment<'a>),
}

// -----------------------------------------------------------------------------

pub fn ws<'a, O, F>(f: F) -> impl Fn(Span<'a>) -> IResult<Span<'a>, (O, Vec<WhiteSpace<'a>>)>
where
    F: Fn(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (s, x) = f(s)?;
        let (s, y) = many0(white_space)(s)?;
        Ok((s, (x, y)))
    }
}

pub fn symbol<'a>(t: &'a str) -> impl Fn(Span<'a>) -> IResult<Span<'a>, Symbol<'a>> {
    move |s: Span<'a>| map(ws(tag(t.clone())), |x| Symbol { nodes: x })(s)
}

pub fn paren<'a, O, F>(f: F) -> impl Fn(Span<'a>) -> IResult<Span<'a>, O>
where
    F: Fn(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (s, _) = symbol("(")(s)?;
        let (s, x) = f(s)?;
        let (s, _) = symbol(")")(s)?;
        Ok((s, x))
    }
}

pub fn bracket<'a, O, F>(f: F) -> impl Fn(Span<'a>) -> IResult<Span<'a>, O>
where
    F: Fn(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (s, _) = symbol("[")(s)?;
        let (s, x) = f(s)?;
        let (s, _) = symbol("]")(s)?;
        Ok((s, x))
    }
}

pub fn brace<'a, O, F>(f: F) -> impl Fn(Span<'a>) -> IResult<Span<'a>, O>
where
    F: Fn(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (s, _) = symbol("{")(s)?;
        let (s, x) = f(s)?;
        let (s, _) = symbol("}")(s)?;
        Ok((s, x))
    }
}

pub fn apostrophe_brace<'a, O, F>(f: F) -> impl Fn(Span<'a>) -> IResult<Span<'a>, O>
where
    F: Fn(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        let (s, _) = symbol("'{")(s)?;
        let (s, x) = f(s)?;
        let (s, _) = symbol("}")(s)?;
        Ok((s, x))
    }
}

// -----------------------------------------------------------------------------

pub fn white_space(s: Span) -> IResult<Span, WhiteSpace> {
    alt((
        map(multispace1, |x| WhiteSpace::Space(x)),
        map(comment, |x| WhiteSpace::Comment(x)),
    ))(s)
}

// -----------------------------------------------------------------------------

pub fn concat<'a>(a: Span<'a>, b: Span<'a>) -> Option<Span<'a>> {
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

// -----------------------------------------------------------------------------
