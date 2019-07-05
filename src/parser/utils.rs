use crate::parser::*;
use nom::bytes::complete::*;
use nom::character::complete::*;
use nom::IResult;

// -----------------------------------------------------------------------------

pub fn ws<'a, O, F>(f: F) -> impl Fn(&'a str) -> IResult<&'a str, O>
where
    F: Fn(&'a str) -> IResult<&'a str, O>,
{
    move |s: &'a str| {
        let (s, _) = space0(s)?;
        let (s, x) = f(s)?;
        let (s, _) = space0(s)?;
        Ok((s, x))
    }
}

pub fn symbol<'a>(t: &'a str) -> impl Fn(&'a str) -> IResult<&'a str, &'a str> {
    move |s: &'a str| ws(tag(t.clone()))(s)
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

#[derive(Debug)]
pub struct DriveStrength<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct Delay3<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct DelayControl<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct StatementOrNull<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct Statement<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct FunctionStatement<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct DelayOrEventControl<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct DynamicArrayNew<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct ClassNew<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct BlockItemDeclaration<'a> {
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

pub fn drive_strength(s: &str) -> IResult<&str, DriveStrength> {
    Ok((s, DriveStrength { raw: vec![] }))
}

pub fn delay3(s: &str) -> IResult<&str, Delay3> {
    Ok((s, Delay3 { raw: vec![] }))
}

pub fn delay_control(s: &str) -> IResult<&str, DelayControl> {
    Ok((s, DelayControl { raw: vec![] }))
}

pub fn statement_or_null(s: &str) -> IResult<&str, StatementOrNull> {
    Ok((s, StatementOrNull { raw: vec![] }))
}

pub fn statement(s: &str) -> IResult<&str, Statement> {
    Ok((s, Statement { raw: vec![] }))
}

pub fn function_statement(s: &str) -> IResult<&str, FunctionStatement> {
    Ok((s, FunctionStatement { raw: vec![] }))
}

pub fn delay_or_event_control(s: &str) -> IResult<&str, DelayOrEventControl> {
    Ok((s, DelayOrEventControl { raw: vec![] }))
}

pub fn dynamic_array_new(s: &str) -> IResult<&str, DynamicArrayNew> {
    Ok((s, DynamicArrayNew { raw: vec![] }))
}

pub fn class_new(s: &str) -> IResult<&str, ClassNew> {
    Ok((s, ClassNew { raw: vec![] }))
}

pub fn block_item_declaration(s: &str) -> IResult<&str, BlockItemDeclaration> {
    Ok((s, BlockItemDeclaration { raw: vec![] }))
}
