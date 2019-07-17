use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum StatementOrNull<'a> {
    Statement(Statement<'a>),
    Attribute(StatementOrNullAttribute<'a>),
}

#[derive(Debug, Node)]
pub struct StatementOrNullAttribute<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct Statement<'a> {
    pub nodes: (
        Option<(BlockIdentifier<'a>, Symbol<'a>)>,
        Vec<AttributeInstance<'a>>,
        StatementItem<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum StatementItem<'a> {
    BlockingAssignment(Box<(BlockingAssignment<'a>, Symbol<'a>)>),
    NonblockingAssignment(Box<(NonblockingAssignment<'a>, Symbol<'a>)>),
    ProceduralContinuousAssignment(Box<(ProceduralContinuousAssignment<'a>, Symbol<'a>)>),
    CaseStatement(Box<CaseStatement<'a>>),
    ConditionalStatement(Box<ConditionalStatement<'a>>),
    IncOrDecExpression(Box<(IncOrDecExpression<'a>, Symbol<'a>)>),
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
    ClockingDrive(Box<(ClockingDrive<'a>, Symbol<'a>)>),
    RandsequenceStatement(Box<RandsequenceStatement<'a>>),
    RandcaseStatement(Box<RandcaseStatement<'a>>),
    ExpectPropertyStatement(Box<ExpectPropertyStatement<'a>>),
}

#[derive(Debug, Node)]
pub struct FunctionStatement<'a> {
    pub nodes: (Statement<'a>,),
}

#[derive(Debug, Node)]
pub enum FunctionStatementOrNull<'a> {
    Statement(FunctionStatement<'a>),
    Attribute(FunctionStatementOrNullAttribute<'a>),
}

#[derive(Debug, Node)]
pub struct FunctionStatementOrNullAttribute<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct VariableIdentifierList<'a> {
    pub nodes: (List<Symbol<'a>, VariableIdentifier<'a>>,),
}

// -----------------------------------------------------------------------------

#[trace]
pub fn statement_or_null(s: Span) -> IResult<Span, StatementOrNull> {
    alt((
        map(statement, |x| StatementOrNull::Statement(x)),
        statement_or_null_attribute,
    ))(s)
}

#[trace]
pub fn statement_or_null_attribute(s: Span) -> IResult<Span, StatementOrNull> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol(";")(s)?;
    Ok((
        s,
        StatementOrNull::Attribute(StatementOrNullAttribute { nodes: (a, b) }),
    ))
}

#[trace]
pub fn statement(s: Span) -> IResult<Span, Statement> {
    let (s, a) = opt(pair(block_identifier, symbol(":")))(s)?;
    let (s, b) = many0(attribute_instance)(s)?;
    let (s, c) = statement_item(s)?;
    Ok((s, Statement { nodes: (a, b, c) }))
}

#[trace]
pub fn statement_item(s: Span) -> IResult<Span, StatementItem> {
    alt((
        map(pair(blocking_assignment, symbol(";")), |x| {
            StatementItem::BlockingAssignment(Box::new(x))
        }),
        map(pair(nonblocking_assignment, symbol(";")), |x| {
            StatementItem::NonblockingAssignment(Box::new(x))
        }),
        map(pair(procedural_continuous_assignment, symbol(";")), |x| {
            StatementItem::ProceduralContinuousAssignment(Box::new(x))
        }),
        map(case_statement, |x| {
            StatementItem::CaseStatement(Box::new(x))
        }),
        map(conditional_statement, |x| {
            StatementItem::ConditionalStatement(Box::new(x))
        }),
        map(pair(inc_or_dec_expression, symbol(";")), |x| {
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
        map(pair(clocking_drive, symbol(";")), |x| {
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

#[trace]
pub fn function_statement(s: Span) -> IResult<Span, FunctionStatement> {
    let (s, a) = statement(s)?;
    Ok((s, FunctionStatement { nodes: (a,) }))
}

#[trace]
pub fn function_statement_or_null(s: Span) -> IResult<Span, FunctionStatementOrNull> {
    alt((
        map(function_statement, |x| {
            FunctionStatementOrNull::Statement(x)
        }),
        function_statement_or_null_attribute,
    ))(s)
}

#[trace]
pub fn function_statement_or_null_attribute(s: Span) -> IResult<Span, FunctionStatementOrNull> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol(";")(s)?;
    Ok((
        s,
        FunctionStatementOrNull::Attribute(FunctionStatementOrNullAttribute { nodes: (a, b) }),
    ))
}

#[trace]
pub fn variable_identifier_list(s: Span) -> IResult<Span, VariableIdentifierList> {
    let (s, a) = list(symbol(","), variable_identifier)(s)?;
    Ok((s, VariableIdentifierList { nodes: (a,) }))
}
