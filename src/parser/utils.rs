use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::bytes::complete::*;
use nom::character::complete::*;
use nom::combinator::*;
use nom::error::*;
use nom::multi::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct Symbol<'a> {
    pub nodes: (Span<'a>, Vec<WhiteSpace<'a>>),
}

#[derive(Debug, Node)]
pub enum WhiteSpace<'a> {
    Space(Span<'a>),
    Comment(Comment<'a>),
}

#[derive(Debug)]
pub struct Paren<'a, T: 'a> {
    pub nodes: (Symbol<'a>, T, Symbol<'a>),
}

#[derive(Debug)]
pub struct Brace<'a, T: 'a> {
    pub nodes: (Symbol<'a>, T, Symbol<'a>),
}

#[derive(Debug)]
pub struct Bracket<'a, T: 'a> {
    pub nodes: (Symbol<'a>, T, Symbol<'a>),
}

#[derive(Debug)]
pub struct ApostropheBrace<'a, T: 'a> {
    pub nodes: (Symbol<'a>, T, Symbol<'a>),
}

#[derive(Debug)]
pub struct List<T, U> {
    pub nodes: (U, Vec<(T, U)>),
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

pub fn paren<'a, O, F>(f: F) -> impl Fn(Span<'a>) -> IResult<Span<'a>, Paren<O>>
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

pub fn bracket<'a, O, F>(f: F) -> impl Fn(Span<'a>) -> IResult<Span<'a>, Bracket<O>>
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

pub fn brace<'a, O, F>(f: F) -> impl Fn(Span<'a>) -> IResult<Span<'a>, Brace<O>>
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

pub fn apostrophe_brace<'a, O, F>(
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

pub fn list<'a, O1, O2, F, G>(f: F, g: G) -> impl Fn(Span<'a>) -> IResult<Span<'a>, List<O1, O2>>
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
                let (u, c) = g(t)?;
                s = u;
                ret.push((b, c));
            } else {
                break;
            }
        }
        Ok((s, List { nodes: (a, ret) }))
    }
}

pub fn rec<'a, O, F>(f: F, id: u32) -> impl Fn(Span<'a>) -> IResult<Span<'a>, O>
where
    F: Fn(Span<'a>) -> IResult<Span<'a>, O>,
{
    move |s: Span<'a>| {
        if check_bit(s, id) {
            return Err(Err::Error(make_error(s, ErrorKind::Fix)));
        }
        let s = set_bit(s, id, true);
        let (s, x) = f(s)?;
        let s = set_bit(s, id, false);
        Ok((s, x))
    }
}

pub fn triple<'a, O1, O2, O3, F, G, H>(
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

pub fn check_bit(s: Span, id: u32) -> bool {
    ((s.extra >> id) & 1) == 1
}

pub fn set_bit(s: Span, id: u32, bit: bool) -> Span {
    let val = if bit { 1u64 << id } else { 0u64 };
    let mask = !(1u64 << id);
    let val = (s.extra & mask) | val;
    Span {
        offset: s.offset,
        line: s.line,
        fragment: s.fragment,
        extra: val,
    }
}

// -----------------------------------------------------------------------------

#[cfg(test)]
macro_rules! parser_test {
    ( $x:expr, $y:expr, $z:pat ) => {
        let ret = all_consuming($x)(Span::new_extra($y, 0));
        if let $z = ret {
        } else {
            assert!(false, "{:?}", ret)
        }
    };
}
