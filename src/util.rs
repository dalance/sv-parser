use crate::identifier::*;
use nom::character::complete::*;
use nom::IResult;

// -----------------------------------------------------------------------------

pub fn sp<'a, O, F>(f: F) -> impl Fn(&'a str) -> IResult<&'a str, O>
where
    F: Fn(&'a str) -> IResult<&'a str, O>,
{
    move |s: &'a str| {
        let (s, _) = space0(s)?;
        let (s, x) = f(s)?;
        Ok((s, x))
    }
}

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct ConstantBitSelect<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct ConstantExpression<'a> {
    pub raw: Vec<&'a str>,
}

pub fn implicit_class_handle(s: &str) -> IResult<&str, Scope> {
    Ok((s, Scope::ImplicitClassHandle))
}

pub fn class_scope(s: &str) -> IResult<&str, Scope> {
    Ok((s, Scope::ClassScope))
}

pub fn constant_bit_select(s: &str) -> IResult<&str, ConstantBitSelect> {
    Ok((s, ConstantBitSelect { raw: vec![] }))
}

pub fn constant_expression(s: &str) -> IResult<&str, ConstantExpression> {
    Ok((s, ConstantExpression { raw: vec![] }))
}
