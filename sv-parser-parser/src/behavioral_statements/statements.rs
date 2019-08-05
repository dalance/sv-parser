use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn statement_or_null(s: Span) -> IResult<Span, StatementOrNull> {
    alt((
        map(statement, |x| StatementOrNull::Statement(Box::new(x))),
        statement_or_null_attribute,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn statement_or_null_attribute(s: Span) -> IResult<Span, StatementOrNull> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol(";")(s)?;
    Ok((
        s,
        StatementOrNull::Attribute(Box::new(StatementOrNullAttribute { nodes: (a, b) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn statement(s: Span) -> IResult<Span, Statement> {
    let (s, a) = opt(pair(block_identifier, symbol(":")))(s)?;
    let (s, b) = many0(attribute_instance)(s)?;
    let (s, c) = statement_item(s)?;
    Ok((s, Statement { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn statement_item(s: Span) -> IResult<Span, StatementItem> {
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn function_statement(s: Span) -> IResult<Span, FunctionStatement> {
    let (s, a) = statement(s)?;
    Ok((s, FunctionStatement { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn function_statement_or_null(s: Span) -> IResult<Span, FunctionStatementOrNull> {
    alt((
        map(function_statement, |x| {
            FunctionStatementOrNull::Statement(Box::new(x))
        }),
        function_statement_or_null_attribute,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn function_statement_or_null_attribute(
    s: Span,
) -> IResult<Span, FunctionStatementOrNull> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol(";")(s)?;
    Ok((
        s,
        FunctionStatementOrNull::Attribute(Box::new(FunctionStatementOrNullAttribute {
            nodes: (a, b),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn variable_identifier_list(s: Span) -> IResult<Span, VariableIdentifierList> {
    let (s, a) = list(symbol(","), variable_identifier)(s)?;
    Ok((s, VariableIdentifierList { nodes: (a,) }))
}
