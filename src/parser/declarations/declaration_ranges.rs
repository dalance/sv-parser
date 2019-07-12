use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum UnpackedDimension<'a> {
    Range(UnpackedDimensionRange<'a>),
    Expression(UnpackedDimensionExpression<'a>),
}

#[derive(Debug, Node)]
pub struct UnpackedDimensionRange<'a> {
    pub nodes: (Bracket<'a, ConstantRange<'a>>,),
}

#[derive(Debug, Node)]
pub struct UnpackedDimensionExpression<'a> {
    pub nodes: (Bracket<'a, ConstantExpression<'a>>,),
}

#[derive(Debug, Node)]
pub enum PackedDimension<'a> {
    Range(PackedDimensionRange<'a>),
    Unsized(UnsizedDimension<'a>),
}

#[derive(Debug, Node)]
pub struct PackedDimensionRange<'a> {
    pub nodes: (Bracket<'a, ConstantRange<'a>>,),
}

#[derive(Debug, Node)]
pub enum AssociativeDimension<'a> {
    DataType(AssociativeDimensionDataType<'a>),
    Asterisk(AssociativeDimensionAsterisk<'a>),
}

#[derive(Debug, Node)]
pub struct AssociativeDimensionDataType<'a> {
    pub nodes: (Bracket<'a, DataType<'a>>,),
}

#[derive(Debug, Node)]
pub struct AssociativeDimensionAsterisk<'a> {
    pub nodes: (Bracket<'a, Symbol<'a>>,),
}

#[derive(Debug, Node)]
pub enum VariableDimension<'a> {
    UnsizedDimension(UnsizedDimension<'a>),
    UnpackedDimension(UnpackedDimension<'a>),
    AssociativeDimension(AssociativeDimension<'a>),
    QueueDimension(QueueDimension<'a>),
}

#[derive(Debug, Node)]
pub struct QueueDimension<'a> {
    pub nodes: (Bracket<'a, (Symbol<'a>, Option<(Symbol<'a>, ConstantExpression<'a>)>)>,),
}

#[derive(Debug, Node)]
pub struct UnsizedDimension<'a> {
    pub nodes: ((Symbol<'a>, Symbol<'a>),),
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
