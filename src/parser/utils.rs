use crate::parser::*;
use nom::bytes::complete::*;
use nom::character::complete::*;
use nom::combinator::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct Symbol<'a> {
    pub nodes: (&'a str,),
}

// -----------------------------------------------------------------------------

pub fn ws<'a, O, F>(f: F) -> impl Fn(&'a str) -> IResult<&'a str, O>
where
    F: Fn(&'a str) -> IResult<&'a str, O>,
{
    move |s: &'a str| {
        let (s, _) = space0(s)?;
        let (s, x) = f(s)?;
        let (s, _) = space0(s)?;
        Ok((s, x))
    }
}

pub fn symbol<'a>(t: &'a str) -> impl Fn(&'a str) -> IResult<&'a str, Symbol<'a>> {
    move |s: &'a str| ws(map(tag(t.clone()), |x| Symbol { nodes: (x,) }))(s)
}

pub fn paren<'a, O, F>(f: F) -> impl Fn(&'a str) -> IResult<&'a str, O>
where
    F: Fn(&'a str) -> IResult<&'a str, O>,
{
    move |s: &'a str| {
        let (s, _) = symbol("(")(s)?;
        let (s, x) = f(s)?;
        let (s, _) = symbol(")")(s)?;
        Ok((s, x))
    }
}

pub fn bracket<'a, O, F>(f: F) -> impl Fn(&'a str) -> IResult<&'a str, O>
where
    F: Fn(&'a str) -> IResult<&'a str, O>,
{
    move |s: &'a str| {
        let (s, _) = symbol("[")(s)?;
        let (s, x) = f(s)?;
        let (s, _) = symbol("]")(s)?;
        Ok((s, x))
    }
}

pub fn brace<'a, O, F>(f: F) -> impl Fn(&'a str) -> IResult<&'a str, O>
where
    F: Fn(&'a str) -> IResult<&'a str, O>,
{
    move |s: &'a str| {
        let (s, _) = symbol("{")(s)?;
        let (s, x) = f(s)?;
        let (s, _) = symbol("}")(s)?;
        Ok((s, x))
    }
}

pub fn apostrophe_brace<'a, O, F>(f: F) -> impl Fn(&'a str) -> IResult<&'a str, O>
where
    F: Fn(&'a str) -> IResult<&'a str, O>,
{
    move |s: &'a str| {
        let (s, _) = symbol("'{")(s)?;
        let (s, x) = f(s)?;
        let (s, _) = symbol("}")(s)?;
        Ok((s, x))
    }
}

// -----------------------------------------------------------------------------
