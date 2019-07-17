use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

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
    UnsizedDimension(UnsizedDimension<'a>),
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
    pub nodes: (Symbol<'a>, Symbol<'a>),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn unpacked_dimension(s: Span) -> IResult<Span, UnpackedDimension> {
    alt((unpacked_dimension_range, unpacked_dimension_expression))(s)
}

#[parser]
pub fn unpacked_dimension_range(s: Span) -> IResult<Span, UnpackedDimension> {
    let (s, a) = bracket(constant_range)(s)?;
    Ok((
        s,
        UnpackedDimension::Range(UnpackedDimensionRange { nodes: (a,) }),
    ))
}

#[parser]
pub fn unpacked_dimension_expression(s: Span) -> IResult<Span, UnpackedDimension> {
    let (s, a) = bracket(constant_expression)(s)?;
    Ok((
        s,
        UnpackedDimension::Expression(UnpackedDimensionExpression { nodes: (a,) }),
    ))
}

#[parser]
pub fn packed_dimension(s: Span) -> IResult<Span, PackedDimension> {
    alt((
        packed_dimension_range,
        map(unsized_dimension, |x| PackedDimension::UnsizedDimension(x)),
    ))(s)
}

#[parser]
pub fn packed_dimension_range(s: Span) -> IResult<Span, PackedDimension> {
    let (s, a) = bracket(constant_range)(s)?;
    Ok((
        s,
        PackedDimension::Range(PackedDimensionRange { nodes: (a,) }),
    ))
}

#[parser]
pub fn associative_dimension(s: Span) -> IResult<Span, AssociativeDimension> {
    alt((
        associative_dimension_data_type,
        associative_dimension_asterisk,
    ))(s)
}

#[parser]
pub fn associative_dimension_data_type(s: Span) -> IResult<Span, AssociativeDimension> {
    let (s, a) = bracket(data_type)(s)?;
    Ok((
        s,
        AssociativeDimension::DataType(AssociativeDimensionDataType { nodes: (a,) }),
    ))
}

#[parser]
pub fn associative_dimension_asterisk(s: Span) -> IResult<Span, AssociativeDimension> {
    let (s, a) = bracket(symbol("*"))(s)?;
    Ok((
        s,
        AssociativeDimension::Asterisk(AssociativeDimensionAsterisk { nodes: (a,) }),
    ))
}

#[parser]
pub fn variable_dimension(s: Span) -> IResult<Span, VariableDimension> {
    alt((
        map(unsized_dimension, |x| {
            VariableDimension::UnsizedDimension(x)
        }),
        map(unpacked_dimension, |x| {
            VariableDimension::UnpackedDimension(x)
        }),
        map(associative_dimension, |x| {
            VariableDimension::AssociativeDimension(x)
        }),
        map(queue_dimension, |x| VariableDimension::QueueDimension(x)),
    ))(s)
}

#[parser]
pub fn queue_dimension(s: Span) -> IResult<Span, QueueDimension> {
    let (s, a) = bracket(pair(
        symbol("$"),
        opt(pair(symbol(":"), constant_expression)),
    ))(s)?;
    Ok((s, QueueDimension { nodes: (a,) }))
}

#[parser]
pub fn unsized_dimension(s: Span) -> IResult<Span, UnsizedDimension> {
    let (s, a) = symbol("[")(s)?;
    let (s, b) = symbol("]")(s)?;
    Ok((s, UnsizedDimension { nodes: (a, b) }))
}
