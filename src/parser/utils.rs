use crate::parser::*;
use nom::bytes::complete::*;
use nom::character::complete::*;
use nom::combinator::*;
use nom::IResult;

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

#[derive(Debug)]
pub struct Symbol<'a> {
    pub nodes: (&'a str,),
}

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct ConstraintBlock<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct EdgeIdentifier<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct IncOrDecDeclaration<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct CheckerInstantiation<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct DataDeclaration<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct ModuleOrGenerateItem<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct InterfaceOrGenerateItem<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct CheckerOrGenerateItem<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct RandomQualifier<'a> {
    pub raw: Vec<&'a str>,
}

pub fn constraint_block(s: &str) -> IResult<&str, ConstraintBlock> {
    Ok((s, ConstraintBlock { raw: vec![] }))
}

pub fn identifier_list(s: &str) -> IResult<&str, Vec<Identifier>> {
    Ok((s, vec![]))
}

pub fn edge_identifier(s: &str) -> IResult<&str, EdgeIdentifier> {
    Ok((s, EdgeIdentifier { raw: vec![] }))
}

pub fn inc_or_dec_declaration(s: &str) -> IResult<&str, IncOrDecDeclaration> {
    Ok((s, IncOrDecDeclaration { raw: vec![] }))
}

pub fn checker_instantiation(s: &str) -> IResult<&str, CheckerInstantiation> {
    Ok((s, CheckerInstantiation { raw: vec![] }))
}

pub fn data_declaration(s: &str) -> IResult<&str, DataDeclaration> {
    Ok((s, DataDeclaration { raw: vec![] }))
}

pub fn module_or_generate_item(s: &str) -> IResult<&str, ModuleOrGenerateItem> {
    Ok((s, ModuleOrGenerateItem { raw: vec![] }))
}

pub fn interface_or_generate_item(s: &str) -> IResult<&str, InterfaceOrGenerateItem> {
    Ok((s, InterfaceOrGenerateItem { raw: vec![] }))
}

pub fn checker_or_generate_item(s: &str) -> IResult<&str, CheckerOrGenerateItem> {
    Ok((s, CheckerOrGenerateItem { raw: vec![] }))
}

pub fn random_qualifier(s: &str) -> IResult<&str, RandomQualifier> {
    Ok((s, RandomQualifier { raw: vec![] }))
}
