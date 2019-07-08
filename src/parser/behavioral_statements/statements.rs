use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum StatementOrNull<'a> {
    Statement(Statement<'a>),
    Attribute(Vec<AttributeInstance<'a>>),
}

#[derive(Debug)]
pub struct Statement<'a> {
    pub nodes: (
        Option<BlockIdentifier<'a>>,
        Vec<AttributeInstance<'a>>,
        StatementItem<'a>,
    ),
}

#[derive(Debug)]
pub enum StatementItem<'a> {
    BlockingAssignment(Box<BlockingAssignment<'a>>),
    NonblockingAssignment(Box<NonblockingAssignment<'a>>),
    ProceduralContinuousAssignment(Box<ProceduralContinuousAssignment<'a>>),
    CaseStatement(Box<CaseStatement<'a>>),
    ConditionalStatement(Box<ConditionalStatement<'a>>),
    IncOrDecExpression(Box<IncOrDecExpression<'a>>),
    SubroutineCallStatement(Box<SubroutineCallStatement<'a>>),
    DisableStatement(Box<DisableStatement<'a>>),
    EventTrigger(Box<EventTrigger<'a>>),
    LoopStatement(Box<LoopStatement<'a>>),
    JumpStatement(Box<JumpStatement<'a>>),
    ParBlock(Box<ParBlock<'a>>),
    ProceduralTimingControlStatement(Box<ProceduralTimingControlStatement<'a>>),
    SeqBlock(Box<SeqBlock<'a>>),
    WaitStatement(Box<WaitStatement<'a>>),
    ProceduralAssertionStatement(Box<ProceduralAssertionStatement<'a>>),
    ClockingDrive(Box<ClockingDrive<'a>>),
    RandsequenceStatement(Box<RandsequenceStatement<'a>>),
    RandcaseStatement(Box<RandcaseStatement<'a>>),
    ExpectPropertyStatement(Box<ExpectPropertyStatement<'a>>),
}

#[derive(Debug)]
pub struct FunctionStatement<'a> {
    pub nodes: (Statement<'a>,),
}

#[derive(Debug)]
pub enum FunctionStatementOrNull<'a> {
    Statement(FunctionStatement<'a>),
    Attribute(Vec<AttributeInstance<'a>>),
}

#[derive(Debug)]
pub struct VariableIdentifierList<'a> {
    pub nodes: (Vec<VariableIdentifier<'a>>,),
}

// -----------------------------------------------------------------------------

pub fn statement_or_null(s: &str) -> IResult<&str, StatementOrNull> {
    alt((
        map(statement, |x| StatementOrNull::Statement(x)),
        map(terminated(many0(attribute_instance), symbol(";")), |x| {
            StatementOrNull::Attribute(x)
        }),
    ))(s)
}

pub fn statement(s: &str) -> IResult<&str, Statement> {
    let (s, x) = opt(terminated(block_identifier, symbol(":")))(s)?;
    let (s, y) = many0(attribute_instance)(s)?;
    let (s, z) = statement_item(s)?;
    Ok((s, Statement { nodes: (x, y, z) }))
}

pub fn statement_item(s: &str) -> IResult<&str, StatementItem> {
    alt((
        map(terminated(blocking_assignment, symbol(";")), |x| {
            StatementItem::BlockingAssignment(Box::new(x))
        }),
        map(terminated(nonblocking_assignment, symbol(";")), |x| {
            StatementItem::NonblockingAssignment(Box::new(x))
        }),
        map(
            terminated(procedural_continuous_assignment, symbol(";")),
            |x| StatementItem::ProceduralContinuousAssignment(Box::new(x)),
        ),
        map(case_statement, |x| {
            StatementItem::CaseStatement(Box::new(x))
        }),
        map(conditional_statement, |x| {
            StatementItem::ConditionalStatement(Box::new(x))
        }),
        map(terminated(inc_or_dec_expression, symbol(";")), |x| {
            StatementItem::IncOrDecExpression(Box::new(x))
        }),
        map(subroutine_call_statement, |x| {
            StatementItem::SubroutineCallStatement(Box::new(x))
        }),
        map(disable_statement, |x| {
            StatementItem::DisableStatement(Box::new(x))
        }),
        map(event_trigger, |x| StatementItem::EventTrigger(Box::new(x))),
        map(loop_statement, |x| {
            StatementItem::LoopStatement(Box::new(x))
        }),
        map(jump_statement, |x| {
            StatementItem::JumpStatement(Box::new(x))
        }),
        map(par_block, |x| StatementItem::ParBlock(Box::new(x))),
        map(procedural_timing_control_statement, |x| {
            StatementItem::ProceduralTimingControlStatement(Box::new(x))
        }),
        map(seq_block, |x| StatementItem::SeqBlock(Box::new(x))),
        map(wait_statement, |x| {
            StatementItem::WaitStatement(Box::new(x))
        }),
        map(procedural_assertion_statement, |x| {
            StatementItem::ProceduralAssertionStatement(Box::new(x))
        }),
        map(terminated(clocking_drive, symbol(";")), |x| {
            StatementItem::ClockingDrive(Box::new(x))
        }),
        map(randsequence_statement, |x| {
            StatementItem::RandsequenceStatement(Box::new(x))
        }),
        map(randcase_statement, |x| {
            StatementItem::RandcaseStatement(Box::new(x))
        }),
        map(expect_property_statement, |x| {
            StatementItem::ExpectPropertyStatement(Box::new(x))
        }),
    ))(s)
}

pub fn function_statement(s: &str) -> IResult<&str, FunctionStatement> {
    let (s, x) = statement(s)?;
    Ok((s, FunctionStatement { nodes: (x,) }))
}

pub fn function_statement_or_null(s: &str) -> IResult<&str, FunctionStatementOrNull> {
    alt((
        map(function_statement, |x| {
            FunctionStatementOrNull::Statement(x)
        }),
        map(terminated(many0(attribute_instance), symbol(";")), |x| {
            FunctionStatementOrNull::Attribute(x)
        }),
    ))(s)
}

pub fn variable_identifier_list(s: &str) -> IResult<&str, VariableIdentifierList> {
    let (s, x) = separated_nonempty_list(symbol(","), variable_identifier)(s)?;
    Ok((s, VariableIdentifierList { nodes: (x,) }))
}
