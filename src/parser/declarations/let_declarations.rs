use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct LetDeclaration<'a> {
    pub nodes: (LetIdentifier<'a>, Option<LetPortList<'a>>, Expression<'a>),
}

#[derive(Debug, Node)]
pub struct LetIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct LetPortList<'a> {
    pub nodes: (Vec<LetPortItem<'a>>,),
}

#[derive(Debug, Node)]
pub struct LetPortItem<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        LetFormalType<'a>,
        Identifier<'a>,
        Vec<VariableDimension<'a>>,
        Option<Expression<'a>>,
    ),
}

#[derive(Debug, Node)]
pub enum LetFormalType<'a> {
    DataTypeOrImplicit(DataTypeOrImplicit<'a>),
    Untyped(Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct LetExpression<'a> {
    pub nodes: (
        Option<PackageScope<'a>>,
        LetIdentifier<'a>,
        Option<LetListOfArguments<'a>>,
    ),
}

#[derive(Debug, Node)]
pub enum LetListOfArguments<'a> {
    Ordered(LetListOfArgumentsOrdered<'a>),
    Named(LetListOfArgumentsNamed<'a>),
}

#[derive(Debug, Node)]
pub struct LetListOfArgumentsOrdered<'a> {
    pub nodes: (
        Vec<LetActualArg<'a>>,
        Vec<(Identifier<'a>, LetActualArg<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct LetListOfArgumentsNamed<'a> {
    pub nodes: (Vec<(Identifier<'a>, LetActualArg<'a>)>,),
}

#[derive(Debug, Node)]
pub struct LetActualArg<'a> {
    pub nodes: (Expression<'a>,),
}

// -----------------------------------------------------------------------------

pub fn let_declaration(s: Span) -> IResult<Span, LetDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn let_identifier(s: Span) -> IResult<Span, LetIdentifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn let_port_list(s: Span) -> IResult<Span, LetPortList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn let_port_item(s: Span) -> IResult<Span, LetPortItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn let_formal_type(s: Span) -> IResult<Span, LetFormalType> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn let_expression(s: Span) -> IResult<Span, LetExpression> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn let_list_of_arguments(s: Span) -> IResult<Span, LetListOfArguments> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn let_actual_arg(s: Span) -> IResult<Span, LetActualArg> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}
