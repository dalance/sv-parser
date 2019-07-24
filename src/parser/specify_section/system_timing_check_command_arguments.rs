use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct TimecheckCondition {
    pub nodes: (MintypmaxExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct ControlledReferenceEvent {
    pub nodes: (ControlledTimingCheckEvent,),
}

#[derive(Clone, Debug, Node)]
pub struct DataEvent {
    pub nodes: (TimingCheckEvent,),
}

#[derive(Clone, Debug, Node)]
pub enum DelayedData {
    TerminalIdentifier(Box<TerminalIdentifier>),
    WithMintypmax(Box<DelayedDataWithMintypmax>),
}

#[derive(Clone, Debug, Node)]
pub struct DelayedDataWithMintypmax {
    pub nodes: (TerminalIdentifier, Bracket<ConstantMintypmaxExpression>),
}

#[derive(Clone, Debug, Node)]
pub enum DelayedReference {
    TerminalIdentifier(Box<TerminalIdentifier>),
    WithMintypmax(Box<DelayedReferenceWithMintypmax>),
}

#[derive(Clone, Debug, Node)]
pub struct DelayedReferenceWithMintypmax {
    pub nodes: (TerminalIdentifier, Bracket<ConstantMintypmaxExpression>),
}

#[derive(Clone, Debug, Node)]
pub struct EndEdgeOffset {
    pub nodes: (MintypmaxExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct EventBasedFlag {
    pub nodes: (ConstantExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct Notifier {
    pub nodes: (VariableIdentifier,),
}

#[derive(Clone, Debug, Node)]
pub struct ReferenceEvent {
    pub nodes: (TimingCheckEvent,),
}

#[derive(Clone, Debug, Node)]
pub struct RemainActiveFlag {
    pub nodes: (ConstantMintypmaxExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct TimestampCondition {
    pub nodes: (MintypmaxExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct StartEdgeOffset {
    pub nodes: (MintypmaxExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct Threshold {
    pub nodes: (ConstantExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct TimingCheckLimit {
    pub nodes: (Expression,),
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
        map(terminal_identifier, |x| {
            DelayedData::TerminalIdentifier(Box::new(x))
        }),
        delayed_data_with_mintypmax,
    ))(s)
}

#[parser]
pub fn delayed_data_with_mintypmax(s: Span) -> IResult<Span, DelayedData> {
    let (s, a) = terminal_identifier(s)?;
    let (s, b) = bracket(constant_mintypmax_expression)(s)?;
    Ok((
        s,
        DelayedData::WithMintypmax(Box::new(DelayedDataWithMintypmax { nodes: (a, b) })),
    ))
}

#[parser]
pub fn delayed_reference(s: Span) -> IResult<Span, DelayedReference> {
    alt((
        map(terminal_identifier, |x| {
            DelayedReference::TerminalIdentifier(Box::new(x))
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
        DelayedReference::WithMintypmax(Box::new(DelayedReferenceWithMintypmax { nodes: (a, b) })),
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
