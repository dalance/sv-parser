use crate::*;

// -----------------------------------------------------------------------------

#[parser]
pub(crate) fn unpacked_dimension(s: Span) -> IResult<Span, UnpackedDimension> {
    alt((unpacked_dimension_range, unpacked_dimension_expression))(s)
}

#[parser]
pub(crate) fn unpacked_dimension_range(s: Span) -> IResult<Span, UnpackedDimension> {
    let (s, a) = bracket(constant_range)(s)?;
    Ok((
        s,
        UnpackedDimension::Range(Box::new(UnpackedDimensionRange { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn unpacked_dimension_expression(s: Span) -> IResult<Span, UnpackedDimension> {
    let (s, a) = bracket(constant_expression)(s)?;
    Ok((
        s,
        UnpackedDimension::Expression(Box::new(UnpackedDimensionExpression { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn packed_dimension(s: Span) -> IResult<Span, PackedDimension> {
    alt((
        packed_dimension_range,
        map(unsized_dimension, |x| {
            PackedDimension::UnsizedDimension(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn packed_dimension_range(s: Span) -> IResult<Span, PackedDimension> {
    let (s, a) = bracket(constant_range)(s)?;
    Ok((
        s,
        PackedDimension::Range(Box::new(PackedDimensionRange { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn associative_dimension(s: Span) -> IResult<Span, AssociativeDimension> {
    alt((
        associative_dimension_data_type,
        associative_dimension_asterisk,
    ))(s)
}

#[parser]
pub(crate) fn associative_dimension_data_type(s: Span) -> IResult<Span, AssociativeDimension> {
    let (s, a) = bracket(data_type)(s)?;
    Ok((
        s,
        AssociativeDimension::DataType(Box::new(AssociativeDimensionDataType { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn associative_dimension_asterisk(s: Span) -> IResult<Span, AssociativeDimension> {
    let (s, a) = bracket(symbol("*"))(s)?;
    Ok((
        s,
        AssociativeDimension::Asterisk(Box::new(AssociativeDimensionAsterisk { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn variable_dimension(s: Span) -> IResult<Span, VariableDimension> {
    alt((
        map(unsized_dimension, |x| {
            VariableDimension::UnsizedDimension(Box::new(x))
        }),
        map(unpacked_dimension, |x| {
            VariableDimension::UnpackedDimension(Box::new(x))
        }),
        map(associative_dimension, |x| {
            VariableDimension::AssociativeDimension(Box::new(x))
        }),
        map(queue_dimension, |x| {
            VariableDimension::QueueDimension(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn queue_dimension(s: Span) -> IResult<Span, QueueDimension> {
    let (s, a) = bracket(pair(
        symbol("$"),
        opt(pair(symbol(":"), constant_expression)),
    ))(s)?;
    Ok((s, QueueDimension { nodes: (a,) }))
}

#[parser]
pub(crate) fn unsized_dimension(s: Span) -> IResult<Span, UnsizedDimension> {
    let (s, a) = symbol("[")(s)?;
    let (s, b) = symbol("]")(s)?;
    Ok((s, UnsizedDimension { nodes: (a, b) }))
}
