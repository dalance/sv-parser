use crate::identifiers::*;
use nom::character::complete::*;
use nom::IResult;

// -----------------------------------------------------------------------------

pub fn sp<'a, O, F>(f: F) -> impl Fn(&'a str) -> IResult<&'a str, O>
where
    F: Fn(&'a str) -> IResult<&'a str, O>,
{
    move |s: &'a str| {
        let (s, _) = space0(s)?;
        let (s, x) = f(s)?;
        Ok((s, x))
    }
}

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct ConstantExpression<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct ConstantRangeExpression<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct Concatenation<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct MultipleConcatenation<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct ConstantFunctionCall<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct ConstantLetExpression<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct ConstantMintypmaxExpression<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct Expression<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct CastingType<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct LetExpression<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct ConstantAssignmentPatternExpression<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct TypeReference<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct ModulePathConcatenation<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct ModulePathMultipleConcatenation<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct FunctionSubroutineCall<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct ModulePathMintypmaxExpression<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct PartSelectRange<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct ConstantPartSelectRange<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct EmptyUnpackedArrayConcatenation<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct MintypmaxExpression<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct AssignmentPatternExpression<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct StreamingConcatenation<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct SequenceMethodCall<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct AssignmentPatternExpressionType<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct AssignmentPatternNetLvalue<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct AssignmentPatternVariableLvalue<'a> {
    pub raw: Vec<&'a str>,
}

pub fn class_scope(s: &str) -> IResult<&str, Scope> {
    Ok((s, Scope::ClassScope))
}

pub fn constant_expression(s: &str) -> IResult<&str, ConstantExpression> {
    Ok((s, ConstantExpression { raw: vec![] }))
}

pub fn constant_range_expression(s: &str) -> IResult<&str, ConstantRangeExpression> {
    Ok((s, ConstantRangeExpression { raw: vec![] }))
}

pub fn constant_concatenation(s: &str) -> IResult<&str, Concatenation> {
    Ok((s, Concatenation { raw: vec![] }))
}

pub fn constant_multiple_concatenation(s: &str) -> IResult<&str, MultipleConcatenation> {
    Ok((s, MultipleConcatenation { raw: vec![] }))
}

pub fn constant_function_call(s: &str) -> IResult<&str, ConstantFunctionCall> {
    Ok((s, ConstantFunctionCall { raw: vec![] }))
}

pub fn constant_let_expression(s: &str) -> IResult<&str, ConstantLetExpression> {
    Ok((s, ConstantLetExpression { raw: vec![] }))
}

pub fn constant_mintypmax_expression(s: &str) -> IResult<&str, ConstantMintypmaxExpression> {
    Ok((s, ConstantMintypmaxExpression { raw: vec![] }))
}

pub fn expression(s: &str) -> IResult<&str, Expression> {
    Ok((s, Expression { raw: vec![] }))
}

pub fn casting_type(s: &str) -> IResult<&str, CastingType> {
    Ok((s, CastingType { raw: vec![] }))
}

pub fn let_expression(s: &str) -> IResult<&str, LetExpression> {
    Ok((s, LetExpression { raw: vec![] }))
}

pub fn constant_assignment_pattern_expression(
    s: &str,
) -> IResult<&str, ConstantAssignmentPatternExpression> {
    Ok((s, ConstantAssignmentPatternExpression { raw: vec![] }))
}

pub fn type_reference(s: &str) -> IResult<&str, TypeReference> {
    Ok((s, TypeReference { raw: vec![] }))
}

pub fn module_path_concatenation(s: &str) -> IResult<&str, ModulePathConcatenation> {
    Ok((s, ModulePathConcatenation { raw: vec![] }))
}

pub fn module_path_multiple_concatenation(
    s: &str,
) -> IResult<&str, ModulePathMultipleConcatenation> {
    Ok((s, ModulePathMultipleConcatenation { raw: vec![] }))
}

pub fn function_subroutine_call(s: &str) -> IResult<&str, FunctionSubroutineCall> {
    Ok((s, FunctionSubroutineCall { raw: vec![] }))
}

pub fn module_path_mintypmax_expression(s: &str) -> IResult<&str, ModulePathMintypmaxExpression> {
    Ok((s, ModulePathMintypmaxExpression { raw: vec![] }))
}

pub fn part_select_range(s: &str) -> IResult<&str, PartSelectRange> {
    Ok((s, PartSelectRange { raw: vec![] }))
}

pub fn constant_part_select_range(s: &str) -> IResult<&str, ConstantPartSelectRange> {
    Ok((s, ConstantPartSelectRange { raw: vec![] }))
}

pub fn empty_unpacked_array_concatenation(
    s: &str,
) -> IResult<&str, EmptyUnpackedArrayConcatenation> {
    Ok((s, EmptyUnpackedArrayConcatenation { raw: vec![] }))
}

pub fn concatenation(s: &str) -> IResult<&str, Concatenation> {
    Ok((s, Concatenation { raw: vec![] }))
}

pub fn multiple_concatenation(s: &str) -> IResult<&str, MultipleConcatenation> {
    Ok((s, MultipleConcatenation { raw: vec![] }))
}

pub fn mintypmax_expression(s: &str) -> IResult<&str, MintypmaxExpression> {
    Ok((s, MintypmaxExpression { raw: vec![] }))
}

pub fn assignment_pattern_expression(s: &str) -> IResult<&str, AssignmentPatternExpression> {
    Ok((s, AssignmentPatternExpression { raw: vec![] }))
}

pub fn streaming_concatenation(s: &str) -> IResult<&str, StreamingConcatenation> {
    Ok((s, StreamingConcatenation { raw: vec![] }))
}

pub fn sequence_method_call(s: &str) -> IResult<&str, SequenceMethodCall> {
    Ok((s, SequenceMethodCall { raw: vec![] }))
}

pub fn assignment_pattern_expression_type(
    s: &str,
) -> IResult<&str, AssignmentPatternExpressionType> {
    Ok((s, AssignmentPatternExpressionType { raw: vec![] }))
}

pub fn assignment_pattern_net_lvalue(s: &str) -> IResult<&str, AssignmentPatternNetLvalue> {
    Ok((s, AssignmentPatternNetLvalue { raw: vec![] }))
}

pub fn assignment_pattern_variable_lvalue(
    s: &str,
) -> IResult<&str, AssignmentPatternVariableLvalue> {
    Ok((s, AssignmentPatternVariableLvalue { raw: vec![] }))
}
