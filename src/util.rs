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
pub struct AssignmentPatternExpression<'a> {
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

#[derive(Debug)]
pub struct CondPredicate<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct DataType<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct OperatorAssignment<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct OpenRangeList<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct ClockingEvent<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct ConstraintBlock<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct SimpleType<'a> {
    pub raw: Vec<&'a str>,
}

pub fn class_scope(s: &str) -> IResult<&str, Scope> {
    Ok((s, Scope::ClassScope))
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

pub fn assignment_pattern_expression(s: &str) -> IResult<&str, AssignmentPatternExpression> {
    Ok((s, AssignmentPatternExpression { raw: vec![] }))
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

pub fn cond_predicate(s: &str) -> IResult<&str, CondPredicate> {
    Ok((s, CondPredicate { raw: vec![] }))
}

pub fn data_type(s: &str) -> IResult<&str, DataType> {
    Ok((s, DataType { raw: vec![] }))
}

pub fn operator_assignment(s: &str) -> IResult<&str, OperatorAssignment> {
    Ok((s, OperatorAssignment { raw: vec![] }))
}

pub fn open_range_list(s: &str) -> IResult<&str, OpenRangeList> {
    Ok((s, OpenRangeList { raw: vec![] }))
}

pub fn clocking_event(s: &str) -> IResult<&str, ClockingEvent> {
    Ok((s, ClockingEvent { raw: vec![] }))
}

pub fn constraint_block(s: &str) -> IResult<&str, ConstraintBlock> {
    Ok((s, ConstraintBlock { raw: vec![] }))
}

pub fn variable_identifier_list(s: &str) -> IResult<&str, Vec<Identifier>> {
    Ok((s, vec![]))
}

pub fn identifier_list(s: &str) -> IResult<&str, Vec<Identifier>> {
    Ok((s, vec![]))
}

pub fn simple_type(s: &str) -> IResult<&str, SimpleType> {
    Ok((s, SimpleType { raw: vec![] }))
}
