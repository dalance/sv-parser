use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct Concatenation<'a> {
    pub nodes: (
        Symbol<'a>,
        Expression<'a>,
        Vec<(Symbol<'a>, Expression<'a>)>,
        Symbol<'a>,
    ),
}

#[derive(Debug)]
pub struct ConstantConcatenation<'a> {
    pub nodes: (
        Symbol<'a>,
        ConstantExpression<'a>,
        Vec<(Symbol<'a>, ConstantExpression<'a>)>,
        Symbol<'a>,
    ),
}

#[derive(Debug)]
pub struct ConstantMultipleConcatenation<'a> {
    pub nodes: (
        Symbol<'a>,
        ConstantExpression<'a>,
        ConstantConcatenation<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug)]
pub struct ModulePathConcatenation<'a> {
    pub nodes: (
        Symbol<'a>,
        ModulePathExpression<'a>,
        Vec<(Symbol<'a>, ModulePathExpression<'a>)>,
        Symbol<'a>,
    ),
}

#[derive(Debug)]
pub struct ModulePathMultipleConcatenation<'a> {
    pub nodes: (
        Symbol<'a>,
        ConstantExpression<'a>,
        ModulePathConcatenation<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug)]
pub struct MultipleConcatenation<'a> {
    pub nodes: (Symbol<'a>, Expression<'a>, Concatenation<'a>, Symbol<'a>),
}

#[derive(Debug)]
pub struct StreamingConcatenation<'a> {
    pub nodes: (
        Symbol<'a>,
        StreamOperator<'a>,
        Option<SliceSize<'a>>,
        StreamConcatenation<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug)]
pub struct StreamOperator<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug)]
pub enum SliceSize<'a> {
    SimpleType(SimpleType<'a>),
    ConstantExpression(ConstantExpression<'a>),
}

#[derive(Debug)]
pub struct StreamConcatenation<'a> {
    pub nodes: (
        Symbol<'a>,
        StreamExpression<'a>,
        Vec<(Symbol<'a>, StreamExpression<'a>)>,
        Symbol<'a>,
    ),
}

#[derive(Debug)]
pub struct StreamExpression<'a> {
    pub nodes: (
        Expression<'a>,
        Option<(
            Symbol<'a>,
            (Symbol<'a>, ArrayRangeExpression<'a>, Symbol<'a>),
        )>,
    ),
}

#[derive(Debug)]
pub enum ArrayRangeExpression<'a> {
    Expression(Expression<'a>),
    Colon(ArrayRangeExpressionColon<'a>),
    PlusColon(ArrayRangeExpressionPlusColon<'a>),
    MinusColon(ArrayRangeExpressionMinusColon<'a>),
}

#[derive(Debug)]
pub struct ArrayRangeExpressionColon<'a> {
    pub nodes: (Expression<'a>, Symbol<'a>, Expression<'a>),
}

#[derive(Debug)]
pub struct ArrayRangeExpressionPlusColon<'a> {
    pub nodes: (Expression<'a>, Symbol<'a>, Expression<'a>),
}

#[derive(Debug)]
pub struct ArrayRangeExpressionMinusColon<'a> {
    pub nodes: (Expression<'a>, Symbol<'a>, Expression<'a>),
}

#[derive(Debug)]
pub struct EmptyUnpackedArrayConcatenation<'a> {
    pub nodes: (Symbol<'a>, Symbol<'a>),
}

// -----------------------------------------------------------------------------

pub fn concatenation(s: Span) -> IResult<Span, Concatenation> {
    let (s, a) = symbol("{")(s)?;
    let (s, b) = expression(s)?;
    let (s, c) = many0(pair(symbol(","), expression))(s)?;
    let (s, d) = symbol("}")(s)?;
    Ok((
        s,
        Concatenation {
            nodes: (a, b, c, d),
        },
    ))
}

pub fn constant_concatenation(s: Span) -> IResult<Span, ConstantConcatenation> {
    let (s, a) = symbol("{")(s)?;
    let (s, b) = constant_expression(s)?;
    let (s, c) = many0(pair(symbol(","), constant_expression))(s)?;
    let (s, d) = symbol("}")(s)?;
    Ok((
        s,
        ConstantConcatenation {
            nodes: (a, b, c, d),
        },
    ))
}

pub fn constant_multiple_concatenation(s: Span) -> IResult<Span, ConstantMultipleConcatenation> {
    let (s, a) = symbol("{")(s)?;
    let (s, b) = constant_expression(s)?;
    let (s, c) = constant_concatenation(s)?;
    let (s, d) = symbol("}")(s)?;
    Ok((
        s,
        ConstantMultipleConcatenation {
            nodes: (a, b, c, d),
        },
    ))
}

pub fn module_path_concatenation(s: Span) -> IResult<Span, ModulePathConcatenation> {
    let (s, a) = symbol("{")(s)?;
    let (s, b) = module_path_expression(s)?;
    let (s, c) = many0(pair(symbol(","), module_path_expression))(s)?;
    let (s, d) = symbol("}")(s)?;
    Ok((
        s,
        ModulePathConcatenation {
            nodes: (a, b, c, d),
        },
    ))
}

pub fn module_path_multiple_concatenation(
    s: Span,
) -> IResult<Span, ModulePathMultipleConcatenation> {
    let (s, a) = symbol("{")(s)?;
    let (s, b) = constant_expression(s)?;
    let (s, c) = module_path_concatenation(s)?;
    let (s, d) = symbol("}")(s)?;
    Ok((
        s,
        ModulePathMultipleConcatenation {
            nodes: (a, b, c, d),
        },
    ))
}

pub fn multiple_concatenation(s: Span) -> IResult<Span, MultipleConcatenation> {
    let (s, a) = symbol("{")(s)?;
    let (s, b) = expression(s)?;
    let (s, c) = concatenation(s)?;
    let (s, d) = symbol("}")(s)?;
    Ok((
        s,
        MultipleConcatenation {
            nodes: (a, b, c, d),
        },
    ))
}

pub fn streaming_concatenation(s: Span) -> IResult<Span, StreamingConcatenation> {
    let (s, a) = symbol("{")(s)?;
    let (s, b) = stream_operator(s)?;
    let (s, c) = opt(slice_size)(s)?;
    let (s, d) = stream_concatenation(s)?;
    let (s, e) = symbol("}")(s)?;
    Ok((
        s,
        StreamingConcatenation {
            nodes: (a, b, c, d, e),
        },
    ))
}

pub fn stream_operator(s: Span) -> IResult<Span, StreamOperator> {
    alt((
        map(symbol(">>"), |x| StreamOperator { nodes: (x,) }),
        map(symbol("<<"), |x| StreamOperator { nodes: (x,) }),
    ))(s)
}

pub fn slice_size(s: Span) -> IResult<Span, SliceSize> {
    alt((
        map(simple_type, |x| SliceSize::SimpleType(x)),
        map(constant_expression, |x| SliceSize::ConstantExpression(x)),
    ))(s)
}

pub fn stream_concatenation(s: Span) -> IResult<Span, StreamConcatenation> {
    let (s, a) = symbol("{")(s)?;
    let (s, b) = stream_expression(s)?;
    let (s, c) = many0(pair(symbol(","), stream_expression))(s)?;
    let (s, d) = symbol("}")(s)?;
    Ok((
        s,
        StreamConcatenation {
            nodes: (a, b, c, d),
        },
    ))
}

pub fn stream_expression(s: Span) -> IResult<Span, StreamExpression> {
    let (s, a) = expression(s)?;
    let (s, b) = opt(pair(symbol("with"), bracket2(array_range_expression)))(s)?;
    Ok((s, StreamExpression { nodes: (a, b) }))
}

pub fn array_range_expression(s: Span) -> IResult<Span, ArrayRangeExpression> {
    alt((
        map(expression, |x| ArrayRangeExpression::Expression(x)),
        array_range_expression_colon,
        array_range_expression_plus_colon,
        array_range_expression_minus_colon,
    ))(s)
}

pub fn array_range_expression_colon(s: Span) -> IResult<Span, ArrayRangeExpression> {
    let (s, a) = expression(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = expression(s)?;
    Ok((
        s,
        ArrayRangeExpression::Colon(ArrayRangeExpressionColon { nodes: (a, b, c) }),
    ))
}

pub fn array_range_expression_plus_colon(s: Span) -> IResult<Span, ArrayRangeExpression> {
    let (s, a) = expression(s)?;
    let (s, b) = symbol("+:")(s)?;
    let (s, c) = expression(s)?;
    Ok((
        s,
        ArrayRangeExpression::PlusColon(ArrayRangeExpressionPlusColon { nodes: (a, b, c) }),
    ))
}

pub fn array_range_expression_minus_colon(s: Span) -> IResult<Span, ArrayRangeExpression> {
    let (s, a) = expression(s)?;
    let (s, b) = symbol("-:")(s)?;
    let (s, c) = expression(s)?;
    Ok((
        s,
        ArrayRangeExpression::MinusColon(ArrayRangeExpressionMinusColon { nodes: (a, b, c) }),
    ))
}

pub fn empty_unpacked_array_concatenation(
    s: Span,
) -> IResult<Span, EmptyUnpackedArrayConcatenation> {
    let (s, a) = symbol("{")(s)?;
    let (s, b) = symbol("}")(s)?;
    Ok((s, EmptyUnpackedArrayConcatenation { nodes: (a, b) }))
}

// -----------------------------------------------------------------------------
