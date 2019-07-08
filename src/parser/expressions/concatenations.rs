use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct Concatenation<'a> {
    pub nodes: (Vec<Expression<'a>>,),
}

#[derive(Debug)]
pub struct ConstantConcatenation<'a> {
    pub nodes: (Vec<ConstantExpression<'a>>,),
}

#[derive(Debug)]
pub struct ConstantMultipleConcatenation<'a> {
    pub nodes: (ConstantExpression<'a>, ConstantConcatenation<'a>),
}

#[derive(Debug)]
pub struct ModulePathConcatenation<'a> {
    pub nodes: (Vec<ModulePathExpression<'a>>,),
}

#[derive(Debug)]
pub struct ModulePathMultipleConcatenation<'a> {
    pub nodes: (ConstantExpression<'a>, ModulePathConcatenation<'a>),
}

#[derive(Debug)]
pub struct MultipleConcatenation<'a> {
    pub nodes: (Expression<'a>, Concatenation<'a>),
}

#[derive(Debug)]
pub struct StreamingConcatenation<'a> {
    pub nodes: (Operator<'a>, Option<SliceSize<'a>>, StreamConcatenation<'a>),
}

#[derive(Debug)]
pub enum SliceSize<'a> {
    Type(SimpleType<'a>),
    Expression(ConstantExpression<'a>),
}

#[derive(Debug)]
pub struct StreamConcatenation<'a> {
    pub nodes: (Vec<StreamExpression<'a>>,),
}

#[derive(Debug)]
pub struct StreamExpression<'a> {
    pub nodes: (Expression<'a>, Option<ArrayRangeExpression<'a>>),
}

#[derive(Debug)]
pub struct ArrayRangeExpression<'a> {
    pub nodes: (Expression<'a>, Option<Operator<'a>>, Option<Expression<'a>>),
}

// -----------------------------------------------------------------------------

pub fn concatenation(s: &str) -> IResult<&str, Concatenation> {
    let (s, x) = brace(separated_nonempty_list(symbol(","), expression))(s)?;
    Ok((s, Concatenation { nodes: (x,) }))
}

pub fn constant_concatenation(s: &str) -> IResult<&str, ConstantConcatenation> {
    let (s, x) = brace(separated_nonempty_list(symbol(","), constant_expression))(s)?;
    Ok((s, ConstantConcatenation { nodes: (x,) }))
}

pub fn constant_multiple_concatenation(s: &str) -> IResult<&str, ConstantMultipleConcatenation> {
    let (s, _) = symbol("{")(s)?;
    let (s, x) = constant_expression(s)?;
    let (s, y) = constant_concatenation(s)?;
    let (s, _) = symbol("}")(s)?;
    Ok((s, ConstantMultipleConcatenation { nodes: (x, y) }))
}

pub fn module_path_concatenation(s: &str) -> IResult<&str, ModulePathConcatenation> {
    let (s, x) = brace(separated_nonempty_list(symbol(","), module_path_expression))(s)?;
    Ok((s, ModulePathConcatenation { nodes: (x,) }))
}

pub fn module_path_multiple_concatenation(
    s: &str,
) -> IResult<&str, ModulePathMultipleConcatenation> {
    let (s, _) = symbol("{")(s)?;
    let (s, x) = constant_expression(s)?;
    let (s, y) = module_path_concatenation(s)?;
    let (s, _) = symbol("}")(s)?;
    Ok((s, ModulePathMultipleConcatenation { nodes: (x, y) }))
}

pub fn multiple_concatenation(s: &str) -> IResult<&str, MultipleConcatenation> {
    let (s, _) = symbol("{")(s)?;
    let (s, x) = expression(s)?;
    let (s, y) = concatenation(s)?;
    let (s, _) = symbol("}")(s)?;
    Ok((s, MultipleConcatenation { nodes: (x, y) }))
}

pub fn streaming_concatenation(s: &str) -> IResult<&str, StreamingConcatenation> {
    let (s, _) = symbol("{")(s)?;
    let (s, x) = stream_operator(s)?;
    let (s, y) = opt(slice_size)(s)?;
    let (s, z) = stream_concatenation(s)?;
    let (s, _) = symbol("}")(s)?;
    Ok((s, StreamingConcatenation { nodes: (x, y, z) }))
}

pub fn stream_operator(s: &str) -> IResult<&str, Operator> {
    alt((
        map(symbol(">>"), |x| Operator { nodes: (x,) }),
        map(symbol("<<"), |x| Operator { nodes: (x,) }),
    ))(s)
}

pub fn slice_size(s: &str) -> IResult<&str, SliceSize> {
    alt((
        map(simple_type, |x| SliceSize::Type(x)),
        map(constant_expression, |x| SliceSize::Expression(x)),
    ))(s)
}

pub fn stream_concatenation(s: &str) -> IResult<&str, StreamConcatenation> {
    let (s, x) = brace(separated_nonempty_list(symbol(","), stream_expression))(s)?;
    Ok((s, StreamConcatenation { nodes: (x,) }))
}

pub fn stream_expression(s: &str) -> IResult<&str, StreamExpression> {
    let (s, x) = expression(s)?;
    let (s, y) = opt(preceded(symbol("with"), bracket(array_range_expression)))(s)?;
    Ok((s, StreamExpression { nodes: (x, y) }))
}

pub fn array_range_expression(s: &str) -> IResult<&str, ArrayRangeExpression> {
    let (s, x) = expression(s)?;
    let (s, y) = opt(pair(array_range_expression_operator, expression))(s)?;
    let (y, z) = if let Some((y, z)) = y {
        (Some(y), Some(z))
    } else {
        (None, None)
    };
    Ok((s, ArrayRangeExpression { nodes: (x, y, z) }))
}

pub fn array_range_expression_operator(s: &str) -> IResult<&str, Operator> {
    alt((
        map(symbol(":"), |x| Operator { nodes: (x,) }),
        map(symbol("+:"), |x| Operator { nodes: (x,) }),
        map(symbol("-:"), |x| Operator { nodes: (x,) }),
    ))(s)
}

pub fn empty_unpacked_array_concatenation(s: &str) -> IResult<&str, ()> {
    let (s, _) = symbol("{")(s)?;
    let (s, _) = symbol("}")(s)?;
    Ok((s, ()))
}

// -----------------------------------------------------------------------------
