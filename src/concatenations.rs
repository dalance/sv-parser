use crate::expressions::*;
use crate::util::*;
use nom::branch::*;
use nom::bytes::complete::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct Concatenation<'a> {
    pub expression: Vec<Expression<'a>>,
}

#[derive(Debug)]
pub struct ConstantConcatenation<'a> {
    pub expression: Vec<ConstantExpression<'a>>,
}

#[derive(Debug)]
pub struct ConstantMultipleConcatenation<'a> {
    pub expression: ConstantExpression<'a>,
    pub concatenation: ConstantConcatenation<'a>,
}

#[derive(Debug)]
pub struct ModulePathConcatenation<'a> {
    pub expression: Vec<ModulePathExpression<'a>>,
}

#[derive(Debug)]
pub struct ModulePathMultipleConcatenation<'a> {
    pub expression: ConstantExpression<'a>,
    pub concatenation: ModulePathConcatenation<'a>,
}

#[derive(Debug)]
pub struct MultipleConcatenation<'a> {
    pub expression: Expression<'a>,
    pub concatenation: Concatenation<'a>,
}

#[derive(Debug)]
pub struct StreamingConcatenation<'a> {
    pub operator: &'a str,
    pub size: Option<SliceSize<'a>>,
    pub concatenation: StreamConcatenation<'a>,
}

#[derive(Debug)]
pub enum SliceSize<'a> {
    Type(SimpleType<'a>),
    Expression(ConstantExpression<'a>),
}

#[derive(Debug)]
pub struct StreamConcatenation<'a> {
    pub expression: Vec<StreamExpression<'a>>,
}

#[derive(Debug)]
pub struct StreamExpression<'a> {
    pub expression: Expression<'a>,
    pub with: Option<ArrayRangeExpression<'a>>,
}

#[derive(Debug)]
pub struct ArrayRangeExpression<'a> {
    pub arg0: Expression<'a>,
    pub operator: Option<&'a str>,
    pub arg1: Option<Expression<'a>>,
}

// -----------------------------------------------------------------------------

pub fn concatenation(s: &str) -> IResult<&str, Concatenation> {
    let (s, _) = tag("{")(s)?;
    let (s, expression) = separated_nonempty_list(sp(tag(",")), sp(expression))(s)?;
    let (s, _) = sp(tag("}"))(s)?;
    Ok((s, Concatenation { expression }))
}

pub fn constant_concatenation(s: &str) -> IResult<&str, ConstantConcatenation> {
    let (s, _) = tag("{")(s)?;
    let (s, expression) = separated_nonempty_list(sp(tag(",")), sp(constant_expression))(s)?;
    let (s, _) = sp(tag("}"))(s)?;
    Ok((s, ConstantConcatenation { expression }))
}

pub fn constant_multiple_concatenation(s: &str) -> IResult<&str, ConstantMultipleConcatenation> {
    let (s, _) = tag("{")(s)?;
    let (s, expression) = sp(constant_expression)(s)?;
    let (s, concatenation) = sp(constant_concatenation)(s)?;
    let (s, _) = sp(tag("}"))(s)?;
    Ok((
        s,
        ConstantMultipleConcatenation {
            expression,
            concatenation,
        },
    ))
}

pub fn module_path_concatenation(s: &str) -> IResult<&str, ModulePathConcatenation> {
    let (s, _) = tag("{")(s)?;
    let (s, expression) = separated_nonempty_list(sp(tag(",")), sp(module_path_expression))(s)?;
    let (s, _) = sp(tag("}"))(s)?;
    Ok((s, ModulePathConcatenation { expression }))
}

pub fn module_path_multiple_concatenation(
    s: &str,
) -> IResult<&str, ModulePathMultipleConcatenation> {
    let (s, _) = tag("{")(s)?;
    let (s, expression) = sp(constant_expression)(s)?;
    let (s, concatenation) = sp(module_path_concatenation)(s)?;
    let (s, _) = sp(tag("}"))(s)?;
    Ok((
        s,
        ModulePathMultipleConcatenation {
            expression,
            concatenation,
        },
    ))
}

pub fn multiple_concatenation(s: &str) -> IResult<&str, MultipleConcatenation> {
    let (s, _) = tag("{")(s)?;
    let (s, expression) = sp(expression)(s)?;
    let (s, concatenation) = sp(concatenation)(s)?;
    let (s, _) = sp(tag("}"))(s)?;
    Ok((
        s,
        MultipleConcatenation {
            expression,
            concatenation,
        },
    ))
}

pub fn streaming_concatenation(s: &str) -> IResult<&str, StreamingConcatenation> {
    let (s, _) = tag("{")(s)?;
    let (s, operator) = sp(stream_operator)(s)?;
    let (s, size) = opt(sp(slice_size))(s)?;
    let (s, concatenation) = sp(stream_concatenation)(s)?;
    let (s, _) = sp(tag("}"))(s)?;
    Ok((
        s,
        StreamingConcatenation {
            operator,
            size,
            concatenation,
        },
    ))
}

pub fn stream_operator(s: &str) -> IResult<&str, &str> {
    alt((tag(">>"), tag("<<")))(s)
}

pub fn slice_size(s: &str) -> IResult<&str, SliceSize> {
    alt((
        map(simple_type, |x| SliceSize::Type(x)),
        map(constant_expression, |x| SliceSize::Expression(x)),
    ))(s)
}

pub fn stream_concatenation(s: &str) -> IResult<&str, StreamConcatenation> {
    let (s, _) = tag("{")(s)?;
    let (s, expression) = separated_nonempty_list(sp(tag(",")), sp(stream_expression))(s)?;
    let (s, _) = sp(tag("}"))(s)?;
    Ok((s, StreamConcatenation { expression }))
}

pub fn stream_expression(s: &str) -> IResult<&str, StreamExpression> {
    let (s, expression) = expression(s)?;
    let (s, with) = opt(preceded(
        sp(tag("with")),
        delimited(sp(tag("[")), array_range_expression, sp(tag("]"))),
    ))(s)?;
    Ok((s, StreamExpression { expression, with }))
}

pub fn array_range_expression(s: &str) -> IResult<&str, ArrayRangeExpression> {
    let (s, arg0) = expression(s)?;
    let (s, x) = opt(pair(
        alt((sp(tag(":")), sp(tag("+:")), sp(tag("-:")))),
        sp(expression),
    ))(s)?;
    let (operator, arg1) = if let Some((x, y)) = x {
        (Some(x), Some(y))
    } else {
        (None, None)
    };
    Ok((
        s,
        ArrayRangeExpression {
            arg0,
            operator,
            arg1,
        },
    ))
}

pub fn empty_unpacked_array_concatenation(s: &str) -> IResult<&str, ()> {
    let (s, _) = tag("{")(s)?;
    let (s, _) = sp(tag("}"))(s)?;
    Ok((s, ()))
}

// -----------------------------------------------------------------------------
