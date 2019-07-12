use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum UnpackedDimension<'a> {
    Range(ConstantRange<'a>),
    Expression(ConstantExpression<'a>),
}

#[derive(Debug, Node)]
pub enum PackedDimension<'a> {
    Range(ConstantRange<'a>),
    Unsized(UnsizedDimension<'a>),
}

#[derive(Debug, Node)]
pub enum AssociativeDimension<'a> {
    DataType(DataType<'a>),
    Asterisk(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum VariableDimension<'a> {
    Unsized(UnsizedDimension<'a>),
    Unpacked(UnpackedDimension<'a>),
    Associative(AssociativeDimension<'a>),
    Queue(QueueDimension<'a>),
}

#[derive(Debug, Node)]
pub struct QueueDimension<'a> {
    pub nodes: (Option<ConstantExpression<'a>>,),
}

#[derive(Debug, Node)]
pub struct UnsizedDimension<'a> {
    pub nodes: (Symbol<'a>,),
}

// -----------------------------------------------------------------------------

pub fn unpacked_dimension(s: Span) -> IResult<Span, UnpackedDimension> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn packed_dimension(s: Span) -> IResult<Span, PackedDimension> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn associative_dimension(s: Span) -> IResult<Span, AssociativeDimension> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn variable_dimension(s: Span) -> IResult<Span, VariableDimension> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn queue_dimension(s: Span) -> IResult<Span, QueueDimension> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn unsized_dimension(s: Span) -> IResult<Span, UnsizedDimension> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}
