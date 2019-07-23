use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum UnpackedDimension {
    Range(UnpackedDimensionRange),
    Expression(UnpackedDimensionExpression),
}

#[derive(Debug, Node)]
pub struct UnpackedDimensionRange {
    pub nodes: (Bracket<ConstantRange>,),
}

#[derive(Debug, Node)]
pub struct UnpackedDimensionExpression {
    pub nodes: (Bracket<ConstantExpression>,),
}

#[derive(Debug, Node)]
pub enum PackedDimension {
    Range(PackedDimensionRange),
    UnsizedDimension(UnsizedDimension),
}

#[derive(Debug, Node)]
pub struct PackedDimensionRange {
    pub nodes: (Bracket<ConstantRange>,),
}

#[derive(Debug, Node)]
pub enum AssociativeDimension {
    DataType(AssociativeDimensionDataType),
    Asterisk(AssociativeDimensionAsterisk),
}

#[derive(Debug, Node)]
pub struct AssociativeDimensionDataType {
    pub nodes: (Bracket<DataType>,),
}

#[derive(Debug, Node)]
pub struct AssociativeDimensionAsterisk {
    pub nodes: (Bracket<Symbol>,),
}

#[derive(Debug, Node)]
pub enum VariableDimension {
    UnsizedDimension(UnsizedDimension),
    UnpackedDimension(UnpackedDimension),
    AssociativeDimension(AssociativeDimension),
    QueueDimension(QueueDimension),
}

#[derive(Debug, Node)]
pub struct QueueDimension {
    pub nodes: (Bracket<(Symbol, Option<(Symbol, ConstantExpression)>)>,),
}

#[derive(Debug, Node)]
pub struct UnsizedDimension {
    pub nodes: (Symbol, Symbol),
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
