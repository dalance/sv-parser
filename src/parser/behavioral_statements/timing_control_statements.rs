use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct ProceduralTimingControlStatement<'a> {
    pub control: ProceduralTimingControl<'a>,
    pub statement: StatementOrNull<'a>,
}

#[derive(Debug)]
pub enum DelayOrEventControl<'a> {
    Delay(DelayControl<'a>),
    Event(EventControl<'a>),
    Repeat(DelayOrEventControlRepeat<'a>),
}

#[derive(Debug)]
pub struct DelayOrEventControlRepeat<'a> {
    pub expression: Expression<'a>,
    pub control: EventControl<'a>,
}

#[derive(Debug)]
pub enum DelayControl<'a> {
    Delay(DelayValue<'a>),
    Mintypmax(MintypmaxExpression<'a>),
}

#[derive(Debug)]
pub enum EventControl<'a> {
    EventIdentifier(HierarchicalIdentifier<'a>),
    EventExpression(EventExpression<'a>),
    Asterisk,
    SequenceIdentifier(ScopedIdentifier<'a>),
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
    pub edge: Option<EdgeIdentifier<'a>>,
    pub expression: Expression<'a>,
    pub iff: Option<Expression<'a>>,
}

#[derive(Debug)]
pub struct EventExpressionSequence<'a> {
    pub instance: SequenceInstance<'a>,
    pub iff: Option<Expression<'a>>,
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
    pub expression: Option<Expression<'a>>,
}

#[derive(Debug)]
pub enum WaitStatement<'a> {
    Wait(WaitStatementWait<'a>),
    Fork,
    Order(WaitStatementOrder<'a>),
}

#[derive(Debug)]
pub struct WaitStatementWait<'a> {
    pub expression: Expression<'a>,
    pub statement: StatementOrNull<'a>,
}

#[derive(Debug)]
pub struct WaitStatementOrder<'a> {
    pub identifier: Vec<HierarchicalIdentifier<'a>>,
    pub block: ActionBlock<'a>,
}

#[derive(Debug)]
pub enum EventTrigger<'a> {
    Named(EventTriggerNamed<'a>),
    Nonblocking(EventTriggerNonblocking<'a>),
}

#[derive(Debug)]
pub struct EventTriggerNamed<'a> {
    pub identifier: HierarchicalIdentifier<'a>,
}

#[derive(Debug)]
pub struct EventTriggerNonblocking<'a> {
    pub control: Option<DelayOrEventControl<'a>>,
    pub identifier: HierarchicalIdentifier<'a>,
}

#[derive(Debug)]
pub enum DisableStatement<'a> {
    Task(HierarchicalIdentifier<'a>),
    Block(HierarchicalIdentifier<'a>),
    Fork,
}

// -----------------------------------------------------------------------------

pub fn procedural_timing_control_statement(
    s: &str,
) -> IResult<&str, ProceduralTimingControlStatement> {
    let (s, x) = procedural_timing_control(s)?;
    let (s, y) = statement_or_null(s)?;
    Ok((
        s,
        ProceduralTimingControlStatement {
            control: x,
            statement: y,
        },
    ))
}

pub fn delay_or_event_control(s: &str) -> IResult<&str, DelayOrEventControl> {
    alt((
        map(delay_control, |x| DelayOrEventControl::Delay(x)),
        map(event_control, |x| DelayOrEventControl::Event(x)),
        delay_or_event_control_repeat,
    ))(s)
}

pub fn delay_or_event_control_repeat(s: &str) -> IResult<&str, DelayOrEventControl> {
    let (s, _) = symbol("repeat")(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, x) = expression(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, y) = event_control(s)?;
    Ok((
        s,
        DelayOrEventControl::Repeat(DelayOrEventControlRepeat {
            expression: x,
            control: y,
        }),
    ))
}

pub fn delay_control(s: &str) -> IResult<&str, DelayControl> {
    alt((delay_control_delay, delay_control_mintypmax))(s)
}

pub fn delay_control_delay(s: &str) -> IResult<&str, DelayControl> {
    let (s, _) = symbol("#")(s)?;
    let (s, x) = delay_value(s)?;
    Ok((s, DelayControl::Delay(x)))
}

pub fn delay_control_mintypmax(s: &str) -> IResult<&str, DelayControl> {
    let (s, _) = symbol("#")(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, x) = mintypmax_expression(s)?;
    let (s, _) = symbol(")")(s)?;
    Ok((s, DelayControl::Mintypmax(x)))
}

pub fn event_control(s: &str) -> IResult<&str, EventControl> {
    alt((
        event_control_event_identifier,
        event_control_event_expression,
        event_control_asterisk,
        event_control_sequence_identifier,
    ))(s)
}

pub fn event_control_event_identifier(s: &str) -> IResult<&str, EventControl> {
    let (s, _) = symbol("@")(s)?;
    let (s, x) = hierarchical_event_identifier(s)?;
    Ok((s, EventControl::EventIdentifier(x)))
}

pub fn event_control_event_expression(s: &str) -> IResult<&str, EventControl> {
    let (s, _) = symbol("@")(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, x) = event_expression(s)?;
    let (s, _) = symbol(")")(s)?;
    Ok((s, EventControl::EventExpression(x)))
}

pub fn event_control_asterisk(s: &str) -> IResult<&str, EventControl> {
    let (s, _) = alt((symbol("@*"), preceded(symbol("@"), symbol("(*)"))))(s)?;
    Ok((s, EventControl::Asterisk))
}

pub fn event_control_sequence_identifier(s: &str) -> IResult<&str, EventControl> {
    let (s, _) = symbol("@")(s)?;
    let (s, x) = ps_or_hierarchical_sequence_identifier(s)?;
    Ok((s, EventControl::SequenceIdentifier(x)))
}

pub fn event_expression(s: &str) -> IResult<&str, EventExpression> {
    alt((
        event_expression_expression,
        event_expression_sequence,
        event_expression_or,
        event_expression_comma,
        event_expression_paren,
    ))(s)
}

pub fn event_expression_expression(s: &str) -> IResult<&str, EventExpression> {
    let (s, x) = opt(edge_identifier)(s)?;
    let (s, y) = expression(s)?;
    let (s, z) = opt(preceded(symbol("iff"), expression))(s)?;
    Ok((
        s,
        EventExpression::Expression(Box::new(EventExpressionExpression {
            edge: x,
            expression: y,
            iff: z,
        })),
    ))
}

pub fn event_expression_sequence(s: &str) -> IResult<&str, EventExpression> {
    let (s, x) = sequence_instance(s)?;
    let (s, y) = opt(preceded(symbol("iff"), expression))(s)?;
    Ok((
        s,
        EventExpression::Sequence(Box::new(EventExpressionSequence {
            instance: x,
            iff: y,
        })),
    ))
}

pub fn event_expression_or(s: &str) -> IResult<&str, EventExpression> {
    let (s, x) = event_expression(s)?;
    let (s, _) = symbol("or")(s)?;
    let (s, y) = event_expression(s)?;
    Ok((s, EventExpression::Or(Box::new((x, y)))))
}

pub fn event_expression_comma(s: &str) -> IResult<&str, EventExpression> {
    let (s, x) = event_expression(s)?;
    let (s, _) = symbol(",")(s)?;
    let (s, y) = event_expression(s)?;
    Ok((s, EventExpression::Comma(Box::new((x, y)))))
}

pub fn event_expression_paren(s: &str) -> IResult<&str, EventExpression> {
    let (s, _) = symbol("(")(s)?;
    let (s, x) = event_expression(s)?;
    let (s, _) = symbol(")")(s)?;
    Ok((s, EventExpression::Paren(Box::new(x))))
}

pub fn procedural_timing_control(s: &str) -> IResult<&str, ProceduralTimingControl> {
    alt((
        map(delay_control, |x| ProceduralTimingControl::DelayControl(x)),
        map(event_control, |x| ProceduralTimingControl::EventControl(x)),
        map(cycle_delay, |x| ProceduralTimingControl::CycleDelay(x)),
    ))(s)
}

pub fn jump_statement(s: &str) -> IResult<&str, JumpStatement> {
    alt((
        jump_statement_return,
        jump_statement_break,
        jump_statement_continue,
    ))(s)
}

pub fn jump_statement_return(s: &str) -> IResult<&str, JumpStatement> {
    let (s, _) = symbol("return")(s)?;
    let (s, x) = opt(expression)(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((
        s,
        JumpStatement::Return(JumpStatementReturn { expression: x }),
    ))
}

pub fn jump_statement_break(s: &str) -> IResult<&str, JumpStatement> {
    let (s, _) = symbol("break")(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, JumpStatement::Break))
}

pub fn jump_statement_continue(s: &str) -> IResult<&str, JumpStatement> {
    let (s, _) = symbol("continue")(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, JumpStatement::Continue))
}

pub fn wait_statement(s: &str) -> IResult<&str, WaitStatement> {
    alt((
        wait_statement_wait,
        wait_statement_fork,
        wait_statement_order,
    ))(s)
}

pub fn wait_statement_wait(s: &str) -> IResult<&str, WaitStatement> {
    let (s, _) = symbol("wait")(s)?;
    let (s, x) = paren(expression)(s)?;
    let (s, y) = statement_or_null(s)?;
    Ok((
        s,
        WaitStatement::Wait(WaitStatementWait {
            expression: x,
            statement: y,
        }),
    ))
}

pub fn wait_statement_fork(s: &str) -> IResult<&str, WaitStatement> {
    let (s, _) = symbol("wait")(s)?;
    let (s, _) = symbol("fork")(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, WaitStatement::Fork))
}

pub fn wait_statement_order(s: &str) -> IResult<&str, WaitStatement> {
    let (s, _) = symbol("wait_order")(s)?;
    let (s, x) = paren(separated_nonempty_list(
        symbol(","),
        hierarchical_identifier,
    ))(s)?;
    let (s, y) = action_block(s)?;
    Ok((
        s,
        WaitStatement::Order(WaitStatementOrder {
            identifier: x,
            block: y,
        }),
    ))
}

pub fn event_trigger(s: &str) -> IResult<&str, EventTrigger> {
    alt((event_trigger_named, event_trigger_nonblocking))(s)
}

pub fn event_trigger_named(s: &str) -> IResult<&str, EventTrigger> {
    let (s, _) = symbol("->")(s)?;
    let (s, x) = hierarchical_event_identifier(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, EventTrigger::Named(EventTriggerNamed { identifier: x })))
}

pub fn event_trigger_nonblocking(s: &str) -> IResult<&str, EventTrigger> {
    let (s, _) = symbol("->>")(s)?;
    let (s, x) = opt(delay_or_event_control)(s)?;
    let (s, y) = hierarchical_event_identifier(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((
        s,
        EventTrigger::Nonblocking(EventTriggerNonblocking {
            control: x,
            identifier: y,
        }),
    ))
}

pub fn disable_statement(s: &str) -> IResult<&str, DisableStatement> {
    alt((
        disable_statement_task,
        disable_statement_block,
        disable_statement_fork,
    ))(s)
}

pub fn disable_statement_task(s: &str) -> IResult<&str, DisableStatement> {
    let (s, _) = symbol("disable")(s)?;
    let (s, x) = hierarchical_task_identifier(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, DisableStatement::Task(x)))
}

pub fn disable_statement_block(s: &str) -> IResult<&str, DisableStatement> {
    let (s, _) = symbol("disable")(s)?;
    let (s, x) = hierarchical_block_identifier(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, DisableStatement::Block(x)))
}

pub fn disable_statement_fork(s: &str) -> IResult<&str, DisableStatement> {
    let (s, _) = symbol("disable")(s)?;
    let (s, _) = symbol("fork")(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, DisableStatement::Fork))
}
