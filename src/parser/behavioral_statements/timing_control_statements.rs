use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct ProceduralTimingControlStatement<'a> {
    pub nodes: (ProceduralTimingControl<'a>, StatementOrNull<'a>),
}

#[derive(Debug, Node)]
pub enum DelayOrEventControl<'a> {
    Delay(DelayControl<'a>),
    Event(EventControl<'a>),
    Repeat(DelayOrEventControlRepeat<'a>),
}

#[derive(Debug, Node)]
pub struct DelayOrEventControlRepeat<'a> {
    pub nodes: (Keyword<'a>, Paren<'a, Expression<'a>>, EventControl<'a>),
}

#[derive(Debug, Node)]
pub enum DelayControl<'a> {
    Delay(DelayControlDelay<'a>),
    Mintypmax(DelayControlMintypmax<'a>),
}

#[derive(Debug, Node)]
pub struct DelayControlDelay<'a> {
    pub nodes: (Symbol<'a>, DelayValue<'a>),
}

#[derive(Debug, Node)]
pub struct DelayControlMintypmax<'a> {
    pub nodes: (Symbol<'a>, Paren<'a, MintypmaxExpression<'a>>),
}

#[derive(Debug, Node)]
pub enum EventControl<'a> {
    EventIdentifier(EventControlEventIdentifier<'a>),
    EventExpression(EventControlEventExpression<'a>),
    Asterisk(EventControlAsterisk<'a>),
    ParenAsterisk(EventControlParenAsterisk<'a>),
    SequenceIdentifier(EventControlSequenceIdentifier<'a>),
}

#[derive(Debug, Node)]
pub struct EventControlEventIdentifier<'a> {
    pub nodes: (Symbol<'a>, HierarchicalEventIdentifier<'a>),
}

#[derive(Debug, Node)]
pub struct EventControlEventExpression<'a> {
    pub nodes: (Symbol<'a>, Paren<'a, EventExpression<'a>>),
}

#[derive(Debug, Node)]
pub struct EventControlAsterisk<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub struct EventControlParenAsterisk<'a> {
    pub nodes: (Symbol<'a>, Paren<'a, Symbol<'a>>),
}

#[derive(Debug, Node)]
pub struct EventControlSequenceIdentifier<'a> {
    pub nodes: (Symbol<'a>, PsOrHierarchicalSequenceIdentifier<'a>),
}

#[derive(Debug, Node)]
pub enum EventExpression<'a> {
    Expression(Box<EventExpressionExpression<'a>>),
    Sequence(Box<EventExpressionSequence<'a>>),
    Or(Box<EventExpressionOr<'a>>),
    Comma(Box<EventExpressionComma<'a>>),
    Paren(Box<EventExpressionParen<'a>>),
}

#[derive(Debug, Node)]
pub struct EventExpressionExpression<'a> {
    pub nodes: (
        Option<EdgeIdentifier<'a>>,
        Expression<'a>,
        Option<(Keyword<'a>, Expression<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct EventExpressionSequence<'a> {
    pub nodes: (SequenceInstance<'a>, Option<(Keyword<'a>, Expression<'a>)>),
}

#[derive(Debug, Node)]
pub struct EventExpressionOr<'a> {
    pub nodes: (EventExpression<'a>, Keyword<'a>, EventExpression<'a>),
}

#[derive(Debug, Node)]
pub struct EventExpressionComma<'a> {
    pub nodes: (EventExpression<'a>, Symbol<'a>, EventExpression<'a>),
}

#[derive(Debug, Node)]
pub struct EventExpressionParen<'a> {
    pub nodes: (Paren<'a, EventExpression<'a>>,),
}

#[derive(Debug, Node)]
pub enum ProceduralTimingControl<'a> {
    DelayControl(DelayControl<'a>),
    EventControl(EventControl<'a>),
    CycleDelay(CycleDelay<'a>),
}

#[derive(Debug, Node)]
pub enum JumpStatement<'a> {
    Return(JumpStatementReturn<'a>),
    Break(JumpStatementBreak<'a>),
    Continue(JumpStatementContinue<'a>),
}

#[derive(Debug, Node)]
pub struct JumpStatementReturn<'a> {
    pub nodes: (Keyword<'a>, Option<Expression<'a>>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct JumpStatementBreak<'a> {
    pub nodes: (Keyword<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct JumpStatementContinue<'a> {
    pub nodes: (Keyword<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum WaitStatement<'a> {
    Wait(WaitStatementWait<'a>),
    Fork(WaitStatementFork<'a>),
    Order(WaitStatementOrder<'a>),
}

#[derive(Debug, Node)]
pub struct WaitStatementWait<'a> {
    pub nodes: (Keyword<'a>, Paren<'a, Expression<'a>>, StatementOrNull<'a>),
}

#[derive(Debug, Node)]
pub struct WaitStatementFork<'a> {
    pub nodes: (Keyword<'a>, Keyword<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct WaitStatementOrder<'a> {
    pub nodes: (
        Keyword<'a>,
        Paren<'a, List<Symbol<'a>, HierarchicalIdentifier<'a>>>,
        ActionBlock<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum EventTrigger<'a> {
    Named(EventTriggerNamed<'a>),
    Nonblocking(EventTriggerNonblocking<'a>),
}

#[derive(Debug, Node)]
pub struct EventTriggerNamed<'a> {
    pub nodes: (Symbol<'a>, HierarchicalEventIdentifier<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct EventTriggerNonblocking<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<DelayOrEventControl<'a>>,
        HierarchicalEventIdentifier<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum DisableStatement<'a> {
    Task(DisableStatementTask<'a>),
    Block(DisableStatementBlock<'a>),
    Fork(DisableStatementFork<'a>),
}

#[derive(Debug, Node)]
pub struct DisableStatementTask<'a> {
    pub nodes: (Keyword<'a>, HierarchicalTaskIdentifier<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct DisableStatementBlock<'a> {
    pub nodes: (Keyword<'a>, HierarchicalBlockIdentifier<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct DisableStatementFork<'a> {
    pub nodes: (Keyword<'a>, Keyword<'a>, Symbol<'a>),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn procedural_timing_control_statement(
    s: Span,
) -> IResult<Span, ProceduralTimingControlStatement> {
    let (s, a) = procedural_timing_control(s)?;
    let (s, b) = statement_or_null(s)?;
    Ok((s, ProceduralTimingControlStatement { nodes: (a, b) }))
}

#[parser]
pub fn delay_or_event_control(s: Span) -> IResult<Span, DelayOrEventControl> {
    alt((
        map(delay_control, |x| DelayOrEventControl::Delay(x)),
        map(event_control, |x| DelayOrEventControl::Event(x)),
        delay_or_event_control_repeat,
    ))(s)
}

#[parser]
pub fn delay_or_event_control_repeat(s: Span) -> IResult<Span, DelayOrEventControl> {
    let (s, a) = keyword("repeat")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = event_control(s)?;
    Ok((
        s,
        DelayOrEventControl::Repeat(DelayOrEventControlRepeat { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn delay_control(s: Span) -> IResult<Span, DelayControl> {
    alt((delay_control_delay, delay_control_mintypmax))(s)
}

#[parser]
pub fn delay_control_delay(s: Span) -> IResult<Span, DelayControl> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = delay_value(s)?;
    Ok((s, DelayControl::Delay(DelayControlDelay { nodes: (a, b) })))
}

#[parser]
pub fn delay_control_mintypmax(s: Span) -> IResult<Span, DelayControl> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = paren(mintypmax_expression)(s)?;
    Ok((
        s,
        DelayControl::Mintypmax(DelayControlMintypmax { nodes: (a, b) }),
    ))
}

#[parser]
pub fn event_control(s: Span) -> IResult<Span, EventControl> {
    alt((
        event_control_event_identifier,
        event_control_event_expression,
        event_control_asterisk,
        event_control_paren_asterisk,
        event_control_sequence_identifier,
    ))(s)
}

#[parser]
pub fn event_control_event_identifier(s: Span) -> IResult<Span, EventControl> {
    let (s, a) = symbol("@")(s)?;
    let (s, b) = hierarchical_event_identifier(s)?;
    Ok((
        s,
        EventControl::EventIdentifier(EventControlEventIdentifier { nodes: (a, b) }),
    ))
}

#[parser]
pub fn event_control_event_expression(s: Span) -> IResult<Span, EventControl> {
    let (s, a) = symbol("@")(s)?;
    let (s, b) = paren(event_expression)(s)?;
    Ok((
        s,
        EventControl::EventExpression(EventControlEventExpression { nodes: (a, b) }),
    ))
}

#[parser]
pub fn event_control_asterisk(s: Span) -> IResult<Span, EventControl> {
    let (s, a) = symbol("@*")(s)?;
    Ok((
        s,
        EventControl::Asterisk(EventControlAsterisk { nodes: (a,) }),
    ))
}

#[parser]
pub fn event_control_paren_asterisk(s: Span) -> IResult<Span, EventControl> {
    let (s, a) = symbol("@")(s)?;
    let (s, b) = paren(symbol("*"))(s)?;
    Ok((
        s,
        EventControl::ParenAsterisk(EventControlParenAsterisk { nodes: (a, b) }),
    ))
}

#[parser]
pub fn event_control_sequence_identifier(s: Span) -> IResult<Span, EventControl> {
    let (s, a) = symbol("@")(s)?;
    let (s, b) = ps_or_hierarchical_sequence_identifier(s)?;
    Ok((
        s,
        EventControl::SequenceIdentifier(EventControlSequenceIdentifier { nodes: (a, b) }),
    ))
}

#[parser]
pub fn event_expression(s: Span) -> IResult<Span, EventExpression> {
    alt((
        event_expression_expression,
        event_expression_sequence,
        event_expression_or,
        event_expression_comma,
        event_expression_paren,
    ))(s)
}

#[parser(MaybeRecursive)]
pub fn event_expression_expression(s: Span) -> IResult<Span, EventExpression> {
    let (s, a) = opt(edge_identifier)(s)?;
    let (s, b) = expression(s)?;
    let (s, c) = opt(pair(keyword("iff"), expression))(s)?;
    Ok((
        s,
        EventExpression::Expression(Box::new(EventExpressionExpression { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn event_expression_sequence(s: Span) -> IResult<Span, EventExpression> {
    let (s, a) = sequence_instance(s)?;
    let (s, b) = opt(pair(keyword("iff"), expression))(s)?;
    Ok((
        s,
        EventExpression::Sequence(Box::new(EventExpressionSequence { nodes: (a, b) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn event_expression_or(s: Span) -> IResult<Span, EventExpression> {
    let (s, a) = event_expression(s)?;
    let (s, b) = keyword("or")(s)?;
    let (s, c) = event_expression(s)?;
    Ok((
        s,
        EventExpression::Or(Box::new(EventExpressionOr { nodes: (a, b, c) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn event_expression_comma(s: Span) -> IResult<Span, EventExpression> {
    let (s, a) = event_expression(s)?;
    let (s, b) = symbol(",")(s)?;
    let (s, c) = event_expression(s)?;
    Ok((
        s,
        EventExpression::Comma(Box::new(EventExpressionComma { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn event_expression_paren(s: Span) -> IResult<Span, EventExpression> {
    let (s, a) = paren(event_expression)(s)?;
    Ok((
        s,
        EventExpression::Paren(Box::new(EventExpressionParen { nodes: (a,) })),
    ))
}

#[parser]
pub fn procedural_timing_control(s: Span) -> IResult<Span, ProceduralTimingControl> {
    alt((
        map(delay_control, |x| ProceduralTimingControl::DelayControl(x)),
        map(event_control, |x| ProceduralTimingControl::EventControl(x)),
        map(cycle_delay, |x| ProceduralTimingControl::CycleDelay(x)),
    ))(s)
}

#[parser]
pub fn jump_statement(s: Span) -> IResult<Span, JumpStatement> {
    alt((
        jump_statement_return,
        jump_statement_break,
        jump_statement_continue,
    ))(s)
}

#[parser]
pub fn jump_statement_return(s: Span) -> IResult<Span, JumpStatement> {
    let (s, a) = keyword("return")(s)?;
    let (s, b) = opt(expression)(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        JumpStatement::Return(JumpStatementReturn { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn jump_statement_break(s: Span) -> IResult<Span, JumpStatement> {
    let (s, a) = keyword("break")(s)?;
    let (s, b) = symbol(";")(s)?;
    Ok((
        s,
        JumpStatement::Break(JumpStatementBreak { nodes: (a, b) }),
    ))
}

#[parser]
pub fn jump_statement_continue(s: Span) -> IResult<Span, JumpStatement> {
    let (s, a) = keyword("continue")(s)?;
    let (s, b) = symbol(";")(s)?;
    Ok((
        s,
        JumpStatement::Continue(JumpStatementContinue { nodes: (a, b) }),
    ))
}

#[parser]
pub fn wait_statement(s: Span) -> IResult<Span, WaitStatement> {
    alt((
        wait_statement_wait,
        wait_statement_fork,
        wait_statement_order,
    ))(s)
}

#[parser]
pub fn wait_statement_wait(s: Span) -> IResult<Span, WaitStatement> {
    let (s, a) = keyword("wait")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = statement_or_null(s)?;
    Ok((
        s,
        WaitStatement::Wait(WaitStatementWait { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn wait_statement_fork(s: Span) -> IResult<Span, WaitStatement> {
    let (s, a) = keyword("wait")(s)?;
    let (s, b) = keyword("fork")(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        WaitStatement::Fork(WaitStatementFork { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn wait_statement_order(s: Span) -> IResult<Span, WaitStatement> {
    let (s, a) = keyword("wait_order")(s)?;
    let (s, b) = paren(list(symbol(","), hierarchical_identifier))(s)?;
    let (s, c) = action_block(s)?;
    Ok((
        s,
        WaitStatement::Order(WaitStatementOrder { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn event_trigger(s: Span) -> IResult<Span, EventTrigger> {
    alt((event_trigger_named, event_trigger_nonblocking))(s)
}

#[parser]
pub fn event_trigger_named(s: Span) -> IResult<Span, EventTrigger> {
    let (s, a) = symbol("->")(s)?;
    let (s, b) = hierarchical_event_identifier(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        EventTrigger::Named(EventTriggerNamed { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn event_trigger_nonblocking(s: Span) -> IResult<Span, EventTrigger> {
    let (s, a) = symbol("->>")(s)?;
    let (s, b) = opt(delay_or_event_control)(s)?;
    let (s, c) = hierarchical_event_identifier(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        EventTrigger::Nonblocking(EventTriggerNonblocking {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn disable_statement(s: Span) -> IResult<Span, DisableStatement> {
    alt((
        disable_statement_task,
        disable_statement_block,
        disable_statement_fork,
    ))(s)
}

#[parser]
pub fn disable_statement_task(s: Span) -> IResult<Span, DisableStatement> {
    let (s, a) = keyword("disable")(s)?;
    let (s, b) = hierarchical_task_identifier(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        DisableStatement::Task(DisableStatementTask { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn disable_statement_block(s: Span) -> IResult<Span, DisableStatement> {
    let (s, a) = keyword("disable")(s)?;
    let (s, b) = hierarchical_block_identifier(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        DisableStatement::Block(DisableStatementBlock { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn disable_statement_fork(s: Span) -> IResult<Span, DisableStatement> {
    let (s, a) = keyword("disable")(s)?;
    let (s, b) = keyword("fork")(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        DisableStatement::Fork(DisableStatementFork { nodes: (a, b, c) }),
    ))
}
