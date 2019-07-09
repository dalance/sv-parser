use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct ProceduralTimingControlStatement<'a> {
    pub nodes: (ProceduralTimingControl<'a>, StatementOrNull<'a>),
}

#[derive(Debug)]
pub enum DelayOrEventControl<'a> {
    Delay(DelayControl<'a>),
    Event(EventControl<'a>),
    Repeat(DelayOrEventControlRepeat<'a>),
}

#[derive(Debug)]
pub struct DelayOrEventControlRepeat<'a> {
    pub nodes: (Expression<'a>, EventControl<'a>),
}

#[derive(Debug)]
pub enum DelayControl<'a> {
    Delay(DelayValue<'a>),
    Mintypmax(MintypmaxExpression<'a>),
}

#[derive(Debug)]
pub enum EventControl<'a> {
    EventIdentifier(HierarchicalEventIdentifier<'a>),
    EventExpression(EventExpression<'a>),
    Asterisk,
    SequenceIdentifier(PsOrHierarchicalSequenceIdentifier<'a>),
}

#[derive(Debug)]
pub enum EventExpression<'a> {
    Expression(Box<EventExpressionExpression<'a>>),
    Sequence(Box<EventExpressionSequence<'a>>),
    Or(Box<(EventExpression<'a>, EventExpression<'a>)>),
    Comma(Box<(EventExpression<'a>, EventExpression<'a>)>),
    Paren(Box<EventExpression<'a>>),
}

#[derive(Debug)]
pub struct EventExpressionExpression<'a> {
    pub nodes: (
        Option<EdgeIdentifier<'a>>,
        Expression<'a>,
        Option<Expression<'a>>,
    ),
}

#[derive(Debug)]
pub struct EventExpressionSequence<'a> {
    pub nodes: (SequenceInstance<'a>, Option<Expression<'a>>),
}

#[derive(Debug)]
pub enum ProceduralTimingControl<'a> {
    DelayControl(DelayControl<'a>),
    EventControl(EventControl<'a>),
    CycleDelay(CycleDelay<'a>),
}

#[derive(Debug)]
pub enum JumpStatement<'a> {
    Return(JumpStatementReturn<'a>),
    Break,
    Continue,
}

#[derive(Debug)]
pub struct JumpStatementReturn<'a> {
    pub nodes: (Option<Expression<'a>>,),
}

#[derive(Debug)]
pub enum WaitStatement<'a> {
    Wait(WaitStatementWait<'a>),
    Fork,
    Order(WaitStatementOrder<'a>),
}

#[derive(Debug)]
pub struct WaitStatementWait<'a> {
    pub nodes: (Expression<'a>, StatementOrNull<'a>),
}

#[derive(Debug)]
pub struct WaitStatementOrder<'a> {
    pub nodes: (Vec<HierarchicalIdentifier<'a>>, ActionBlock<'a>),
}

#[derive(Debug)]
pub enum EventTrigger<'a> {
    Named(EventTriggerNamed<'a>),
    Nonblocking(EventTriggerNonblocking<'a>),
}

#[derive(Debug)]
pub struct EventTriggerNamed<'a> {
    pub nodes: (HierarchicalEventIdentifier<'a>,),
}

#[derive(Debug)]
pub struct EventTriggerNonblocking<'a> {
    pub nodes: (
        Option<DelayOrEventControl<'a>>,
        HierarchicalEventIdentifier<'a>,
    ),
}

#[derive(Debug)]
pub enum DisableStatement<'a> {
    Task(HierarchicalTaskIdentifier<'a>),
    Block(HierarchicalBlockIdentifier<'a>),
    Fork,
}

// -----------------------------------------------------------------------------

pub fn procedural_timing_control_statement(
    s: Span,
) -> IResult<Span, ProceduralTimingControlStatement> {
    let (s, x) = procedural_timing_control(s)?;
    let (s, y) = statement_or_null(s)?;
    Ok((s, ProceduralTimingControlStatement { nodes: (x, y) }))
}

pub fn delay_or_event_control(s: Span) -> IResult<Span, DelayOrEventControl> {
    alt((
        map(delay_control, |x| DelayOrEventControl::Delay(x)),
        map(event_control, |x| DelayOrEventControl::Event(x)),
        delay_or_event_control_repeat,
    ))(s)
}

pub fn delay_or_event_control_repeat(s: Span) -> IResult<Span, DelayOrEventControl> {
    let (s, _) = symbol("repeat")(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, x) = expression(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, y) = event_control(s)?;
    Ok((
        s,
        DelayOrEventControl::Repeat(DelayOrEventControlRepeat { nodes: (x, y) }),
    ))
}

pub fn delay_control(s: Span) -> IResult<Span, DelayControl> {
    alt((delay_control_delay, delay_control_mintypmax))(s)
}

pub fn delay_control_delay(s: Span) -> IResult<Span, DelayControl> {
    let (s, _) = symbol("#")(s)?;
    let (s, x) = delay_value(s)?;
    Ok((s, DelayControl::Delay(x)))
}

pub fn delay_control_mintypmax(s: Span) -> IResult<Span, DelayControl> {
    let (s, _) = symbol("#")(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, x) = mintypmax_expression(s)?;
    let (s, _) = symbol(")")(s)?;
    Ok((s, DelayControl::Mintypmax(x)))
}

pub fn event_control(s: Span) -> IResult<Span, EventControl> {
    alt((
        event_control_event_identifier,
        event_control_event_expression,
        event_control_asterisk,
        event_control_sequence_identifier,
    ))(s)
}

pub fn event_control_event_identifier(s: Span) -> IResult<Span, EventControl> {
    let (s, _) = symbol("@")(s)?;
    let (s, x) = hierarchical_event_identifier(s)?;
    Ok((s, EventControl::EventIdentifier(x)))
}

pub fn event_control_event_expression(s: Span) -> IResult<Span, EventControl> {
    let (s, _) = symbol("@")(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, x) = event_expression(s)?;
    let (s, _) = symbol(")")(s)?;
    Ok((s, EventControl::EventExpression(x)))
}

pub fn event_control_asterisk(s: Span) -> IResult<Span, EventControl> {
    let (s, _) = alt((symbol("@*"), preceded(symbol("@"), symbol("(*)"))))(s)?;
    Ok((s, EventControl::Asterisk))
}

pub fn event_control_sequence_identifier(s: Span) -> IResult<Span, EventControl> {
    let (s, _) = symbol("@")(s)?;
    let (s, x) = ps_or_hierarchical_sequence_identifier(s)?;
    Ok((s, EventControl::SequenceIdentifier(x)))
}

pub fn event_expression(s: Span) -> IResult<Span, EventExpression> {
    alt((
        event_expression_expression,
        event_expression_sequence,
        event_expression_or,
        event_expression_comma,
        event_expression_paren,
    ))(s)
}

pub fn event_expression_expression(s: Span) -> IResult<Span, EventExpression> {
    let (s, x) = opt(edge_identifier)(s)?;
    let (s, y) = expression(s)?;
    let (s, z) = opt(preceded(symbol("iff"), expression))(s)?;
    Ok((
        s,
        EventExpression::Expression(Box::new(EventExpressionExpression { nodes: (x, y, z) })),
    ))
}

pub fn event_expression_sequence(s: Span) -> IResult<Span, EventExpression> {
    let (s, x) = sequence_instance(s)?;
    let (s, y) = opt(preceded(symbol("iff"), expression))(s)?;
    Ok((
        s,
        EventExpression::Sequence(Box::new(EventExpressionSequence { nodes: (x, y) })),
    ))
}

pub fn event_expression_or(s: Span) -> IResult<Span, EventExpression> {
    let (s, x) = event_expression(s)?;
    let (s, _) = symbol("or")(s)?;
    let (s, y) = event_expression(s)?;
    Ok((s, EventExpression::Or(Box::new((x, y)))))
}

pub fn event_expression_comma(s: Span) -> IResult<Span, EventExpression> {
    let (s, x) = event_expression(s)?;
    let (s, _) = symbol(",")(s)?;
    let (s, y) = event_expression(s)?;
    Ok((s, EventExpression::Comma(Box::new((x, y)))))
}

pub fn event_expression_paren(s: Span) -> IResult<Span, EventExpression> {
    let (s, _) = symbol("(")(s)?;
    let (s, x) = event_expression(s)?;
    let (s, _) = symbol(")")(s)?;
    Ok((s, EventExpression::Paren(Box::new(x))))
}

pub fn procedural_timing_control(s: Span) -> IResult<Span, ProceduralTimingControl> {
    alt((
        map(delay_control, |x| ProceduralTimingControl::DelayControl(x)),
        map(event_control, |x| ProceduralTimingControl::EventControl(x)),
        map(cycle_delay, |x| ProceduralTimingControl::CycleDelay(x)),
    ))(s)
}

pub fn jump_statement(s: Span) -> IResult<Span, JumpStatement> {
    alt((
        jump_statement_return,
        jump_statement_break,
        jump_statement_continue,
    ))(s)
}

pub fn jump_statement_return(s: Span) -> IResult<Span, JumpStatement> {
    let (s, _) = symbol("return")(s)?;
    let (s, x) = opt(expression)(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((
        s,
        JumpStatement::Return(JumpStatementReturn { nodes: (x,) }),
    ))
}

pub fn jump_statement_break(s: Span) -> IResult<Span, JumpStatement> {
    let (s, _) = symbol("break")(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, JumpStatement::Break))
}

pub fn jump_statement_continue(s: Span) -> IResult<Span, JumpStatement> {
    let (s, _) = symbol("continue")(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, JumpStatement::Continue))
}

pub fn wait_statement(s: Span) -> IResult<Span, WaitStatement> {
    alt((
        wait_statement_wait,
        wait_statement_fork,
        wait_statement_order,
    ))(s)
}

pub fn wait_statement_wait(s: Span) -> IResult<Span, WaitStatement> {
    let (s, _) = symbol("wait")(s)?;
    let (s, x) = paren(expression)(s)?;
    let (s, y) = statement_or_null(s)?;
    Ok((s, WaitStatement::Wait(WaitStatementWait { nodes: (x, y) })))
}

pub fn wait_statement_fork(s: Span) -> IResult<Span, WaitStatement> {
    let (s, _) = symbol("wait")(s)?;
    let (s, _) = symbol("fork")(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, WaitStatement::Fork))
}

pub fn wait_statement_order(s: Span) -> IResult<Span, WaitStatement> {
    let (s, _) = symbol("wait_order")(s)?;
    let (s, x) = paren(separated_nonempty_list(
        symbol(","),
        hierarchical_identifier,
    ))(s)?;
    let (s, y) = action_block(s)?;
    Ok((
        s,
        WaitStatement::Order(WaitStatementOrder { nodes: (x, y) }),
    ))
}

pub fn event_trigger(s: Span) -> IResult<Span, EventTrigger> {
    alt((event_trigger_named, event_trigger_nonblocking))(s)
}

pub fn event_trigger_named(s: Span) -> IResult<Span, EventTrigger> {
    let (s, _) = symbol("->")(s)?;
    let (s, x) = hierarchical_event_identifier(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, EventTrigger::Named(EventTriggerNamed { nodes: (x,) })))
}

pub fn event_trigger_nonblocking(s: Span) -> IResult<Span, EventTrigger> {
    let (s, _) = symbol("->>")(s)?;
    let (s, x) = opt(delay_or_event_control)(s)?;
    let (s, y) = hierarchical_event_identifier(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((
        s,
        EventTrigger::Nonblocking(EventTriggerNonblocking { nodes: (x, y) }),
    ))
}

pub fn disable_statement(s: Span) -> IResult<Span, DisableStatement> {
    alt((
        disable_statement_task,
        disable_statement_block,
        disable_statement_fork,
    ))(s)
}

pub fn disable_statement_task(s: Span) -> IResult<Span, DisableStatement> {
    let (s, _) = symbol("disable")(s)?;
    let (s, x) = hierarchical_task_identifier(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, DisableStatement::Task(x)))
}

pub fn disable_statement_block(s: Span) -> IResult<Span, DisableStatement> {
    let (s, _) = symbol("disable")(s)?;
    let (s, x) = hierarchical_block_identifier(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, DisableStatement::Block(x)))
}

pub fn disable_statement_fork(s: Span) -> IResult<Span, DisableStatement> {
    let (s, _) = symbol("disable")(s)?;
    let (s, _) = symbol("fork")(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, DisableStatement::Fork))
}
