use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct Concatenation {
    pub nodes: (Brace<List<Symbol, Expression>>,),
}

#[derive(Clone, Debug, Node)]
pub struct ConstantConcatenation {
    pub nodes: (Brace<List<Symbol, ConstantExpression>>,),
}

#[derive(Clone, Debug, Node)]
pub struct ConstantMultipleConcatenation {
    pub nodes: (Brace<(ConstantExpression, ConstantConcatenation)>,),
}

#[derive(Clone, Debug, Node)]
pub struct ModulePathConcatenation {
    pub nodes: (Brace<List<Symbol, ModulePathExpression>>,),
}

#[derive(Clone, Debug, Node)]
pub struct ModulePathMultipleConcatenation {
    pub nodes: (Brace<(ConstantExpression, ModulePathConcatenation)>,),
}

#[derive(Clone, Debug, Node)]
pub struct MultipleConcatenation {
    pub nodes: (Brace<(Expression, Concatenation)>,),
}

#[derive(Clone, Debug, Node)]
pub struct StreamingConcatenation {
    pub nodes: (Brace<(StreamOperator, Option<SliceSize>, StreamConcatenation)>,),
}

#[derive(Clone, Debug, Node)]
pub struct StreamOperator {
    pub nodes: (Symbol,),
}

#[derive(Clone, Debug, Node)]
pub enum SliceSize {
    SimpleType(Box<SimpleType>),
    ConstantExpression(Box<ConstantExpression>),
}

#[derive(Clone, Debug, Node)]
pub struct StreamConcatenation {
    pub nodes: (Brace<List<Symbol, StreamExpression>>,),
}

#[derive(Clone, Debug, Node)]
pub struct StreamExpression {
    pub nodes: (Expression, Option<(Keyword, Bracket<ArrayRangeExpression>)>),
}

#[derive(Clone, Debug, Node)]
pub enum ArrayRangeExpression {
    Expression(Box<Expression>),
    Colon(Box<ArrayRangeExpressionColon>),
    PlusColon(Box<ArrayRangeExpressionPlusColon>),
    MinusColon(Box<ArrayRangeExpressionMinusColon>),
}

#[derive(Clone, Debug, Node)]
pub struct ArrayRangeExpressionColon {
    pub nodes: (Expression, Symbol, Expression),
}

#[derive(Clone, Debug, Node)]
pub struct ArrayRangeExpressionPlusColon {
    pub nodes: (Expression, Symbol, Expression),
}

#[derive(Clone, Debug, Node)]
pub struct ArrayRangeExpressionMinusColon {
    pub nodes: (Expression, Symbol, Expression),
}

#[derive(Clone, Debug, Node)]
pub struct EmptyUnpackedArrayConcatenation {
    pub nodes: (Symbol, Symbol),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn concatenation(s: Span) -> IResult<Span, Concatenation> {
    let (s, a) = brace(list(symbol(","), expression))(s)?;
    Ok((s, Concatenation { nodes: (a,) }))
}

#[parser]
pub fn constant_concatenation(s: Span) -> IResult<Span, ConstantConcatenation> {
    let (s, a) = brace(list(symbol(","), constant_expression))(s)?;
    Ok((s, ConstantConcatenation { nodes: (a,) }))
}

#[parser]
pub fn constant_multiple_concatenation(s: Span) -> IResult<Span, ConstantMultipleConcatenation> {
    let (s, a) = brace(pair(constant_expression, constant_concatenation))(s)?;
    Ok((s, ConstantMultipleConcatenation { nodes: (a,) }))
}

#[parser]
pub fn module_path_concatenation(s: Span) -> IResult<Span, ModulePathConcatenation> {
    let (s, a) = brace(list(symbol(","), module_path_expression))(s)?;
    Ok((s, ModulePathConcatenation { nodes: (a,) }))
}

#[parser]
pub fn module_path_multiple_concatenation(
    s: Span,
) -> IResult<Span, ModulePathMultipleConcatenation> {
    let (s, a) = brace(pair(constant_expression, module_path_concatenation))(s)?;
    Ok((s, ModulePathMultipleConcatenation { nodes: (a,) }))
}

#[parser]
pub fn multiple_concatenation(s: Span) -> IResult<Span, MultipleConcatenation> {
    let (s, a) = brace(pair(expression, concatenation))(s)?;
    Ok((s, MultipleConcatenation { nodes: (a,) }))
}

#[parser]
pub fn streaming_concatenation(s: Span) -> IResult<Span, StreamingConcatenation> {
    let (s, a) = brace(triple(
        stream_operator,
        opt(slice_size),
        stream_concatenation,
    ))(s)?;
    Ok((s, StreamingConcatenation { nodes: (a,) }))
}

#[parser]
pub fn stream_operator(s: Span) -> IResult<Span, StreamOperator> {
    alt((
        map(symbol(">>"), |x| StreamOperator { nodes: (x,) }),
        map(symbol("<<"), |x| StreamOperator { nodes: (x,) }),
    ))(s)
}

#[parser]
pub fn slice_size(s: Span) -> IResult<Span, SliceSize> {
    alt((
        map(simple_type, |x| SliceSize::SimpleType(Box::new(x))),
        map(constant_expression, |x| {
            SliceSize::ConstantExpression(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn stream_concatenation(s: Span) -> IResult<Span, StreamConcatenation> {
    let (s, a) = brace(list(symbol(","), stream_expression))(s)?;
    Ok((s, StreamConcatenation { nodes: (a,) }))
}

#[parser(MaybeRecursive)]
pub fn stream_expression(s: Span) -> IResult<Span, StreamExpression> {
    let (s, a) = expression(s)?;
    let (s, b) = opt(pair(keyword("with"), bracket(array_range_expression)))(s)?;
    Ok((s, StreamExpression { nodes: (a, b) }))
}

#[parser]
pub fn array_range_expression(s: Span) -> IResult<Span, ArrayRangeExpression> {
    alt((
        map(expression, |x| {
            ArrayRangeExpression::Expression(Box::new(x))
        }),
        array_range_expression_colon,
        array_range_expression_plus_colon,
        array_range_expression_minus_colon,
    ))(s)
}

#[parser(MaybeRecursive)]
pub fn array_range_expression_colon(s: Span) -> IResult<Span, ArrayRangeExpression> {
    let (s, a) = expression(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = expression(s)?;
    Ok((
        s,
        ArrayRangeExpression::Colon(Box::new(ArrayRangeExpressionColon { nodes: (a, b, c) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn array_range_expression_plus_colon(s: Span) -> IResult<Span, ArrayRangeExpression> {
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

#[parser(MaybeRecursive)]
pub fn array_range_expression_minus_colon(s: Span) -> IResult<Span, ArrayRangeExpression> {
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

#[parser]
pub fn empty_unpacked_array_concatenation(
    s: Span,
) -> IResult<Span, EmptyUnpackedArrayConcatenation> {
    let (s, a) = symbol("{")(s)?;
    let (s, b) = symbol("}")(s)?;
    Ok((s, EmptyUnpackedArrayConcatenation { nodes: (a, b) }))
}

// -----------------------------------------------------------------------------
