use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct TimecheckCondition<'a> {
    pub nodes: (MintypmaxExpression<'a>,),
}

#[derive(Debug, Node)]
pub struct ControlledReferenceEvent<'a> {
    pub nodes: (ControlledTimingCheckEvent<'a>,),
}

#[derive(Debug, Node)]
pub struct DataEvent<'a> {
    pub nodes: (TimingCheckEvent<'a>,),
}

#[derive(Debug, Node)]
pub enum DelayedData<'a> {
    TerminalIdentifier(TerminalIdentifier<'a>),
    WithMintypmax(DelayedDataWithMintypmax<'a>),
}

#[derive(Debug, Node)]
pub struct DelayedDataWithMintypmax<'a> {
    pub nodes: (
        TerminalIdentifier<'a>,
        Bracket<'a, ConstantMintypmaxExpression<'a>>,
    ),
}

#[derive(Debug, Node)]
pub enum DelayedReference<'a> {
    TerminalIdentifier(TerminalIdentifier<'a>),
    WithMintypmax(DelayedReferenceWithMintypmax<'a>),
}

#[derive(Debug, Node)]
pub struct DelayedReferenceWithMintypmax<'a> {
    pub nodes: (
        TerminalIdentifier<'a>,
        Bracket<'a, ConstantMintypmaxExpression<'a>>,
    ),
}

#[derive(Debug, Node)]
pub struct EndEdgeOffset<'a> {
    pub nodes: (MintypmaxExpression<'a>,),
}

#[derive(Debug, Node)]
pub struct EventBasedFlag<'a> {
    pub nodes: (ConstantExpression<'a>,),
}

#[derive(Debug, Node)]
pub struct Notifier<'a> {
    pub nodes: (VariableIdentifier<'a>,),
}

#[derive(Debug, Node)]
pub struct ReferenceEvent<'a> {
    pub nodes: (TimingCheckEvent<'a>,),
}

#[derive(Debug, Node)]
pub struct RemainActiveFlag<'a> {
    pub nodes: (ConstantMintypmaxExpression<'a>,),
}

#[derive(Debug, Node)]
pub struct TimestampCondition<'a> {
    pub nodes: (MintypmaxExpression<'a>,),
}

#[derive(Debug, Node)]
pub struct StartEdgeOffset<'a> {
    pub nodes: (MintypmaxExpression<'a>,),
}

#[derive(Debug, Node)]
pub struct Threshold<'a> {
    pub nodes: (ConstantExpression<'a>,),
}

#[derive(Debug, Node)]
pub struct TimingCheckLimit<'a> {
    pub nodes: (Expression<'a>,),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn timecheck_condition(s: Span) -> IResult<Span, TimecheckCondition> {
    let (s, a) = mintypmax_expression(s)?;
    Ok((s, TimecheckCondition { nodes: (a,) }))
}

#[parser]
pub fn controlled_referecne_event(s: Span) -> IResult<Span, ControlledReferenceEvent> {
    let (s, a) = controlled_timing_check_event(s)?;
    Ok((s, ControlledReferenceEvent { nodes: (a,) }))
}

#[parser]
pub fn data_event(s: Span) -> IResult<Span, DataEvent> {
    let (s, a) = timing_check_event(s)?;
    Ok((s, DataEvent { nodes: (a,) }))
}

#[parser]
pub fn delayed_data(s: Span) -> IResult<Span, DelayedData> {
    alt((
        map(terminal_identifier, |x| DelayedData::TerminalIdentifier(x)),
        delayed_data_with_mintypmax,
    ))(s)
}

#[parser]
pub fn delayed_data_with_mintypmax(s: Span) -> IResult<Span, DelayedData> {
    let (s, a) = terminal_identifier(s)?;
    let (s, b) = bracket(constant_mintypmax_expression)(s)?;
    Ok((
        s,
        DelayedData::WithMintypmax(DelayedDataWithMintypmax { nodes: (a, b) }),
    ))
}

#[parser]
pub fn delayed_reference(s: Span) -> IResult<Span, DelayedReference> {
    alt((
        map(terminal_identifier, |x| {
            DelayedReference::TerminalIdentifier(x)
        }),
        delayed_reference_with_mintypmax,
    ))(s)
}

#[parser]
pub fn delayed_reference_with_mintypmax(s: Span) -> IResult<Span, DelayedReference> {
    let (s, a) = terminal_identifier(s)?;
    let (s, b) = bracket(constant_mintypmax_expression)(s)?;
    Ok((
        s,
        DelayedReference::WithMintypmax(DelayedReferenceWithMintypmax { nodes: (a, b) }),
    ))
}

#[parser]
pub fn end_edge_offset(s: Span) -> IResult<Span, EndEdgeOffset> {
    let (s, a) = mintypmax_expression(s)?;
    Ok((s, EndEdgeOffset { nodes: (a,) }))
}

#[parser]
pub fn event_based_flag(s: Span) -> IResult<Span, EventBasedFlag> {
    let (s, a) = constant_expression(s)?;
    Ok((s, EventBasedFlag { nodes: (a,) }))
}

#[parser]
pub fn notifier(s: Span) -> IResult<Span, Notifier> {
    let (s, a) = variable_identifier(s)?;
    Ok((s, Notifier { nodes: (a,) }))
}

#[parser]
pub fn referecne_event(s: Span) -> IResult<Span, ReferenceEvent> {
    let (s, a) = timing_check_event(s)?;
    Ok((s, ReferenceEvent { nodes: (a,) }))
}

#[parser]
pub fn remain_active_flag(s: Span) -> IResult<Span, RemainActiveFlag> {
    let (s, a) = constant_mintypmax_expression(s)?;
    Ok((s, RemainActiveFlag { nodes: (a,) }))
}

#[parser]
pub fn timestamp_condition(s: Span) -> IResult<Span, TimestampCondition> {
    let (s, a) = mintypmax_expression(s)?;
    Ok((s, TimestampCondition { nodes: (a,) }))
}

#[parser]
pub fn start_edge_offset(s: Span) -> IResult<Span, StartEdgeOffset> {
    let (s, a) = mintypmax_expression(s)?;
    Ok((s, StartEdgeOffset { nodes: (a,) }))
}

#[parser]
pub fn threshold(s: Span) -> IResult<Span, Threshold> {
    let (s, a) = constant_expression(s)?;
    Ok((s, Threshold { nodes: (a,) }))
}

#[parser]
pub fn timing_check_limit(s: Span) -> IResult<Span, TimingCheckLimit> {
    let (s, a) = expression(s)?;
    Ok((s, TimingCheckLimit { nodes: (a,) }))
}
