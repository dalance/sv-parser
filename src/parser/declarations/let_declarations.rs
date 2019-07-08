use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct LetDeclaration<'a> {
    pub nodes: (LetIdentifier<'a>, Option<LetPortList<'a>>, Expression<'a>),
}

#[derive(Debug)]
pub struct LetIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct LetPortList<'a> {
    pub nodes: (Vec<LetPortItem<'a>>,),
}

#[derive(Debug)]
pub struct LetPortItem<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        LetFormalType<'a>,
        Identifier<'a>,
        Vec<VariableDimension<'a>>,
        Option<Expression<'a>>,
    ),
}

#[derive(Debug)]
pub enum LetFormalType<'a> {
    DataTypeOrImplicit(DataTypeOrImplicit<'a>),
    Untyped,
}

#[derive(Debug)]
pub struct LetExpression<'a> {
    pub nodes: (
        Option<PackageScope<'a>>,
        LetIdentifier<'a>,
        Option<LetListOfArguments<'a>>,
    ),
}

#[derive(Debug)]
pub enum LetListOfArguments<'a> {
    Ordered(LetListOfArgumentsOrdered<'a>),
    Named(LetListOfArgumentsNamed<'a>),
}

#[derive(Debug)]
pub struct LetListOfArgumentsOrdered<'a> {
    pub nodes: (
        Vec<LetActualArg<'a>>,
        Vec<(Identifier<'a>, LetActualArg<'a>)>,
    ),
}

#[derive(Debug)]
pub struct LetListOfArgumentsNamed<'a> {
    pub nodes: (Vec<(Identifier<'a>, LetActualArg<'a>)>,),
}

#[derive(Debug)]
pub struct LetActualArg<'a> {
    pub nodes: (Expression<'a>,),
}

// -----------------------------------------------------------------------------

pub fn let_declaration(s: &str) -> IResult<&str, LetDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn let_identifier(s: &str) -> IResult<&str, LetIdentifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn let_port_list(s: &str) -> IResult<&str, LetPortList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn let_port_item(s: &str) -> IResult<&str, LetPortItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn let_formal_type(s: &str) -> IResult<&str, LetFormalType> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn let_expression(s: &str) -> IResult<&str, LetExpression> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn let_list_of_arguments(s: &str) -> IResult<&str, LetListOfArguments> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn let_actual_arg(s: &str) -> IResult<&str, LetActualArg> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}
