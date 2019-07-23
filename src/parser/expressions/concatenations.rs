use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct Concatenation {
    pub nodes: (Brace< List<Symbol, Expression>>,),
}

#[derive(Debug, Node)]
pub struct ConstantConcatenation {
    pub nodes: (Brace< List<Symbol, ConstantExpression>>,),
}

#[derive(Debug, Node)]
pub struct ConstantMultipleConcatenation {
    pub nodes: (Brace< (ConstantExpression, ConstantConcatenation)>,),
}

#[derive(Debug, Node)]
pub struct ModulePathConcatenation {
    pub nodes: (Brace< List<Symbol, ModulePathExpression>>,),
}

#[derive(Debug, Node)]
pub struct ModulePathMultipleConcatenation {
    pub nodes: (Brace< (ConstantExpression, ModulePathConcatenation)>,),
}

#[derive(Debug, Node)]
pub struct MultipleConcatenation {
    pub nodes: (Brace< (Expression, Concatenation)>,),
}

#[derive(Debug, Node)]
pub struct StreamingConcatenation {
    pub nodes: (
        Brace<
            
            (
                StreamOperator,
                Option<SliceSize>,
                StreamConcatenation,
            ),
        >,
    ),
}

#[derive(Debug, Node)]
pub struct StreamOperator {
    pub nodes: (Symbol,),
}

#[derive(Debug, Node)]
pub enum SliceSize {
    SimpleType(SimpleType),
    ConstantExpression(ConstantExpression),
}

#[derive(Debug, Node)]
pub struct StreamConcatenation {
    pub nodes: (Brace< List<Symbol, StreamExpression>>,),
}

#[derive(Debug, Node)]
pub struct StreamExpression {
    pub nodes: (
        Expression,
        Option<(Keyword, Bracket< ArrayRangeExpression>)>,
    ),
}

#[derive(Debug, Node)]
pub enum ArrayRangeExpression {
    Expression(Expression),
    Colon(ArrayRangeExpressionColon),
    PlusColon(ArrayRangeExpressionPlusColon),
    MinusColon(ArrayRangeExpressionMinusColon),
}

#[derive(Debug, Node)]
pub struct ArrayRangeExpressionColon {
    pub nodes: (Expression, Symbol, Expression),
}

#[derive(Debug, Node)]
pub struct ArrayRangeExpressionPlusColon {
    pub nodes: (Expression, Symbol, Expression),
}

#[derive(Debug, Node)]
pub struct ArrayRangeExpressionMinusColon {
    pub nodes: (Expression, Symbol, Expression),
}

#[derive(Debug, Node)]
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

#[parser(Memoize)]
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
        map(simple_type, |x| SliceSize::SimpleType(x)),
        map(constant_expression, |x| SliceSize::ConstantExpression(x)),
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
        map(expression, |x| ArrayRangeExpression::Expression(x)),
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
        ArrayRangeExpression::Colon(ArrayRangeExpressionColon { nodes: (a, b, c) }),
    ))
}

#[parser(MaybeRecursive)]
pub fn array_range_expression_plus_colon(s: Span) -> IResult<Span, ArrayRangeExpression> {
    let (s, a) = expression(s)?;
    let (s, b) = symbol("+:")(s)?;
    let (s, c) = expression(s)?;
    Ok((
        s,
        ArrayRangeExpression::PlusColon(ArrayRangeExpressionPlusColon { nodes: (a, b, c) }),
    ))
}

#[parser(MaybeRecursive)]
pub fn array_range_expression_minus_colon(s: Span) -> IResult<Span, ArrayRangeExpression> {
    let (s, a) = expression(s)?;
    let (s, b) = symbol("-:")(s)?;
    let (s, c) = expression(s)?;
    Ok((
        s,
        ArrayRangeExpression::MinusColon(ArrayRangeExpressionMinusColon { nodes: (a, b, c) }),
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
