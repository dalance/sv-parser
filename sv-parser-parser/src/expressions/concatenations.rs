use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn concatenation(s: Span) -> IResult<Span, Concatenation> {
    let (s, a) = brace(list(symbol(","), expression))(s)?;
    Ok((s, Concatenation { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn constant_concatenation(s: Span) -> IResult<Span, ConstantConcatenation> {
    let (s, a) = brace(list(symbol(","), constant_expression))(s)?;
    Ok((s, ConstantConcatenation { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn constant_multiple_concatenation(
    s: Span,
) -> IResult<Span, ConstantMultipleConcatenation> {
    let (s, a) = brace(pair(constant_expression, constant_concatenation))(s)?;
    Ok((s, ConstantMultipleConcatenation { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn module_path_concatenation(s: Span) -> IResult<Span, ModulePathConcatenation> {
    let (s, a) = brace(list(symbol(","), module_path_expression))(s)?;
    Ok((s, ModulePathConcatenation { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn module_path_multiple_concatenation(
    s: Span,
) -> IResult<Span, ModulePathMultipleConcatenation> {
    let (s, a) = brace(pair(constant_expression, module_path_concatenation))(s)?;
    Ok((s, ModulePathMultipleConcatenation { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn multiple_concatenation(s: Span) -> IResult<Span, MultipleConcatenation> {
    let (s, a) = brace(pair(expression, concatenation))(s)?;
    Ok((s, MultipleConcatenation { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn streaming_concatenation(s: Span) -> IResult<Span, StreamingConcatenation> {
    let (s, a) = brace(triple(
        stream_operator,
        opt(slice_size),
        stream_concatenation,
    ))(s)?;
    Ok((s, StreamingConcatenation { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn stream_operator(s: Span) -> IResult<Span, StreamOperator> {
    alt((
        map(symbol(">>"), |x| StreamOperator { nodes: (x,) }),
        map(symbol("<<"), |x| StreamOperator { nodes: (x,) }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn slice_size(s: Span) -> IResult<Span, SliceSize> {
    alt((
        map(simple_type, |x| SliceSize::SimpleType(Box::new(x))),
        map(constant_expression, |x| {
            SliceSize::ConstantExpression(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn stream_concatenation(s: Span) -> IResult<Span, StreamConcatenation> {
    let (s, a) = brace(list(symbol(","), stream_expression))(s)?;
    Ok((s, StreamConcatenation { nodes: (a,) }))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn stream_expression(s: Span) -> IResult<Span, StreamExpression> {
    let (s, a) = expression(s)?;
    let (s, b) = opt(pair(keyword("with"), bracket(array_range_expression)))(s)?;
    Ok((s, StreamExpression { nodes: (a, b) }))
}

#[tracable_parser]
pub(crate) fn array_range_expression(s: Span) -> IResult<Span, ArrayRangeExpression> {
    alt((
        map(expression, |x| {
            ArrayRangeExpression::Expression(Box::new(x))
        }),
        array_range_expression_colon,
        array_range_expression_plus_colon,
        array_range_expression_minus_colon,
    ))(s)
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn array_range_expression_colon(s: Span) -> IResult<Span, ArrayRangeExpression> {
    let (s, a) = expression(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = expression(s)?;
    Ok((
        s,
        ArrayRangeExpression::Colon(Box::new(ArrayRangeExpressionColon { nodes: (a, b, c) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn array_range_expression_plus_colon(s: Span) -> IResult<Span, ArrayRangeExpression> {
    let (s, a) = expression(s)?;
    let (s, b) = symbol("+:")(s)?;
    let (s, c) = expression(s)?;
    Ok((
        s,
        ArrayRangeExpression::PlusColon(Box::new(ArrayRangeExpressionPlusColon {
            nodes: (a, b, c),
        })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn array_range_expression_minus_colon(s: Span) -> IResult<Span, ArrayRangeExpression> {
    let (s, a) = expression(s)?;
    let (s, b) = symbol("-:")(s)?;
    let (s, c) = expression(s)?;
    Ok((
        s,
        ArrayRangeExpression::MinusColon(Box::new(ArrayRangeExpressionMinusColon {
            nodes: (a, b, c),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn empty_unpacked_array_concatenation(
    s: Span,
) -> IResult<Span, EmptyUnpackedArrayConcatenation> {
    let (s, a) = symbol("{")(s)?;
    let (s, b) = symbol("}")(s)?;
    Ok((s, EmptyUnpackedArrayConcatenation { nodes: (a, b) }))
}
