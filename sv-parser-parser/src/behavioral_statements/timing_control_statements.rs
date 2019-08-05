use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn procedural_timing_control_statement(
    s: Span,
) -> IResult<Span, ProceduralTimingControlStatement> {
    let (s, a) = procedural_timing_control(s)?;
    let (s, b) = statement_or_null(s)?;
    Ok((s, ProceduralTimingControlStatement { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn delay_or_event_control(s: Span) -> IResult<Span, DelayOrEventControl> {
    alt((
        map(delay_control, |x| DelayOrEventControl::Delay(Box::new(x))),
        map(event_control, |x| DelayOrEventControl::Event(Box::new(x))),
        delay_or_event_control_repeat,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn delay_or_event_control_repeat(s: Span) -> IResult<Span, DelayOrEventControl> {
    let (s, a) = keyword("repeat")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = event_control(s)?;
    Ok((
        s,
        DelayOrEventControl::Repeat(Box::new(DelayOrEventControlRepeat { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn delay_control(s: Span) -> IResult<Span, DelayControl> {
    alt((delay_control_delay, delay_control_mintypmax))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn delay_control_delay(s: Span) -> IResult<Span, DelayControl> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = delay_value(s)?;
    Ok((
        s,
        DelayControl::Delay(Box::new(DelayControlDelay { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn delay_control_mintypmax(s: Span) -> IResult<Span, DelayControl> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = paren(mintypmax_expression)(s)?;
    Ok((
        s,
        DelayControl::Mintypmax(Box::new(DelayControlMintypmax { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn event_control(s: Span) -> IResult<Span, EventControl> {
    alt((
        event_control_event_identifier,
        event_control_event_expression,
        event_control_asterisk,
        event_control_paren_asterisk,
        event_control_sequence_identifier,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn event_control_event_identifier(s: Span) -> IResult<Span, EventControl> {
    let (s, a) = symbol("@")(s)?;
    let (s, b) = hierarchical_event_identifier(s)?;
    Ok((
        s,
        EventControl::EventIdentifier(Box::new(EventControlEventIdentifier { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn event_control_event_expression(s: Span) -> IResult<Span, EventControl> {
    let (s, a) = symbol("@")(s)?;
    let (s, b) = paren(event_expression)(s)?;
    Ok((
        s,
        EventControl::EventExpression(Box::new(EventControlEventExpression { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn event_control_asterisk(s: Span) -> IResult<Span, EventControl> {
    let (s, a) = symbol("@*")(s)?;
    Ok((
        s,
        EventControl::Asterisk(Box::new(EventControlAsterisk { nodes: (a,) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn event_control_paren_asterisk(s: Span) -> IResult<Span, EventControl> {
    let (s, a) = symbol("@")(s)?;
    let (s, b) = paren(symbol("*"))(s)?;
    Ok((
        s,
        EventControl::ParenAsterisk(Box::new(EventControlParenAsterisk { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn event_control_sequence_identifier(s: Span) -> IResult<Span, EventControl> {
    let (s, a) = symbol("@")(s)?;
    let (s, b) = ps_or_hierarchical_sequence_identifier(s)?;
    Ok((
        s,
        EventControl::SequenceIdentifier(Box::new(EventControlSequenceIdentifier {
            nodes: (a, b),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn event_expression(s: Span) -> IResult<Span, EventExpression> {
    alt((
        event_expression_or,
        event_expression_comma,
        event_expression_expression,
        event_expression_sequence,
        event_expression_paren,
    ))(s)
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn event_expression_expression(s: Span) -> IResult<Span, EventExpression> {
    let (s, a) = opt(edge_identifier)(s)?;
    let (s, b) = expression(s)?;
    let (s, c) = opt(pair(keyword("iff"), expression))(s)?;
    Ok((
        s,
        EventExpression::Expression(Box::new(EventExpressionExpression { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn event_expression_sequence(s: Span) -> IResult<Span, EventExpression> {
    let (s, a) = sequence_instance(s)?;
    let (s, b) = opt(pair(keyword("iff"), expression))(s)?;
    Ok((
        s,
        EventExpression::Sequence(Box::new(EventExpressionSequence { nodes: (a, b) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn event_expression_or(s: Span) -> IResult<Span, EventExpression> {
    let (s, a) = event_expression(s)?;
    let (s, b) = keyword("or")(s)?;
    let (s, c) = event_expression(s)?;
    Ok((
        s,
        EventExpression::Or(Box::new(EventExpressionOr { nodes: (a, b, c) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn event_expression_comma(s: Span) -> IResult<Span, EventExpression> {
    let (s, a) = event_expression(s)?;
    let (s, b) = symbol(",")(s)?;
    let (s, c) = event_expression(s)?;
    Ok((
        s,
        EventExpression::Comma(Box::new(EventExpressionComma { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn event_expression_paren(s: Span) -> IResult<Span, EventExpression> {
    let (s, a) = paren(event_expression)(s)?;
    Ok((
        s,
        EventExpression::Paren(Box::new(EventExpressionParen { nodes: (a,) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn procedural_timing_control(s: Span) -> IResult<Span, ProceduralTimingControl> {
    alt((
        map(delay_control, |x| {
            ProceduralTimingControl::DelayControl(Box::new(x))
        }),
        map(event_control, |x| {
            ProceduralTimingControl::EventControl(Box::new(x))
        }),
        map(cycle_delay, |x| {
            ProceduralTimingControl::CycleDelay(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn jump_statement(s: Span) -> IResult<Span, JumpStatement> {
    alt((
        jump_statement_return,
        jump_statement_break,
        jump_statement_continue,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn jump_statement_return(s: Span) -> IResult<Span, JumpStatement> {
    let (s, a) = keyword("return")(s)?;
    let (s, b) = opt(expression)(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        JumpStatement::Return(Box::new(JumpStatementReturn { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn jump_statement_break(s: Span) -> IResult<Span, JumpStatement> {
    let (s, a) = keyword("break")(s)?;
    let (s, b) = symbol(";")(s)?;
    Ok((
        s,
        JumpStatement::Break(Box::new(JumpStatementBreak { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn jump_statement_continue(s: Span) -> IResult<Span, JumpStatement> {
    let (s, a) = keyword("continue")(s)?;
    let (s, b) = symbol(";")(s)?;
    Ok((
        s,
        JumpStatement::Continue(Box::new(JumpStatementContinue { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn wait_statement(s: Span) -> IResult<Span, WaitStatement> {
    alt((
        wait_statement_wait,
        wait_statement_fork,
        wait_statement_order,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn wait_statement_wait(s: Span) -> IResult<Span, WaitStatement> {
    let (s, a) = keyword("wait")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = statement_or_null(s)?;
    Ok((
        s,
        WaitStatement::Wait(Box::new(WaitStatementWait { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn wait_statement_fork(s: Span) -> IResult<Span, WaitStatement> {
    let (s, a) = keyword("wait")(s)?;
    let (s, b) = keyword("fork")(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        WaitStatement::Fork(Box::new(WaitStatementFork { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn wait_statement_order(s: Span) -> IResult<Span, WaitStatement> {
    let (s, a) = keyword("wait_order")(s)?;
    let (s, b) = paren(list(symbol(","), hierarchical_identifier))(s)?;
    let (s, c) = action_block(s)?;
    Ok((
        s,
        WaitStatement::Order(Box::new(WaitStatementOrder { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn event_trigger(s: Span) -> IResult<Span, EventTrigger> {
    alt((event_trigger_named, event_trigger_nonblocking))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn event_trigger_named(s: Span) -> IResult<Span, EventTrigger> {
    let (s, a) = symbol("->")(s)?;
    let (s, b) = hierarchical_event_identifier(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        EventTrigger::Named(Box::new(EventTriggerNamed { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn event_trigger_nonblocking(s: Span) -> IResult<Span, EventTrigger> {
    let (s, a) = symbol("->>")(s)?;
    let (s, b) = opt(delay_or_event_control)(s)?;
    let (s, c) = hierarchical_event_identifier(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        EventTrigger::Nonblocking(Box::new(EventTriggerNonblocking {
            nodes: (a, b, c, d),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn disable_statement(s: Span) -> IResult<Span, DisableStatement> {
    alt((
        disable_statement_task,
        disable_statement_block,
        disable_statement_fork,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn disable_statement_task(s: Span) -> IResult<Span, DisableStatement> {
    let (s, a) = keyword("disable")(s)?;
    let (s, b) = hierarchical_task_identifier(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        DisableStatement::Task(Box::new(DisableStatementTask { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn disable_statement_block(s: Span) -> IResult<Span, DisableStatement> {
    let (s, a) = keyword("disable")(s)?;
    let (s, b) = hierarchical_block_identifier(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        DisableStatement::Block(Box::new(DisableStatementBlock { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn disable_statement_fork(s: Span) -> IResult<Span, DisableStatement> {
    let (s, a) = keyword("disable")(s)?;
    let (s, b) = keyword("fork")(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        DisableStatement::Fork(Box::new(DisableStatementFork { nodes: (a, b, c) })),
    ))
}
