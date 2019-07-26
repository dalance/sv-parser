use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn timecheck_condition(s: Span) -> IResult<Span, TimecheckCondition> {
    let (s, a) = mintypmax_expression(s)?;
    Ok((s, TimecheckCondition { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn controlled_referecne_event(s: Span) -> IResult<Span, ControlledReferenceEvent> {
    let (s, a) = controlled_timing_check_event(s)?;
    Ok((s, ControlledReferenceEvent { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn data_event(s: Span) -> IResult<Span, DataEvent> {
    let (s, a) = timing_check_event(s)?;
    Ok((s, DataEvent { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn delayed_data(s: Span) -> IResult<Span, DelayedData> {
    alt((
        map(terminal_identifier, |x| {
            DelayedData::TerminalIdentifier(Box::new(x))
        }),
        delayed_data_with_mintypmax,
    ))(s)
}

#[tracable_parser]
pub(crate) fn delayed_data_with_mintypmax(s: Span) -> IResult<Span, DelayedData> {
    let (s, a) = terminal_identifier(s)?;
    let (s, b) = bracket(constant_mintypmax_expression)(s)?;
    Ok((
        s,
        DelayedData::WithMintypmax(Box::new(DelayedDataWithMintypmax { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn delayed_reference(s: Span) -> IResult<Span, DelayedReference> {
    alt((
        map(terminal_identifier, |x| {
            DelayedReference::TerminalIdentifier(Box::new(x))
        }),
        delayed_reference_with_mintypmax,
    ))(s)
}

#[tracable_parser]
pub(crate) fn delayed_reference_with_mintypmax(s: Span) -> IResult<Span, DelayedReference> {
    let (s, a) = terminal_identifier(s)?;
    let (s, b) = bracket(constant_mintypmax_expression)(s)?;
    Ok((
        s,
        DelayedReference::WithMintypmax(Box::new(DelayedReferenceWithMintypmax { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn end_edge_offset(s: Span) -> IResult<Span, EndEdgeOffset> {
    let (s, a) = mintypmax_expression(s)?;
    Ok((s, EndEdgeOffset { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn event_based_flag(s: Span) -> IResult<Span, EventBasedFlag> {
    let (s, a) = constant_expression(s)?;
    Ok((s, EventBasedFlag { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn notifier(s: Span) -> IResult<Span, Notifier> {
    let (s, a) = variable_identifier(s)?;
    Ok((s, Notifier { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn referecne_event(s: Span) -> IResult<Span, ReferenceEvent> {
    let (s, a) = timing_check_event(s)?;
    Ok((s, ReferenceEvent { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn remain_active_flag(s: Span) -> IResult<Span, RemainActiveFlag> {
    let (s, a) = constant_mintypmax_expression(s)?;
    Ok((s, RemainActiveFlag { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn timestamp_condition(s: Span) -> IResult<Span, TimestampCondition> {
    let (s, a) = mintypmax_expression(s)?;
    Ok((s, TimestampCondition { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn start_edge_offset(s: Span) -> IResult<Span, StartEdgeOffset> {
    let (s, a) = mintypmax_expression(s)?;
    Ok((s, StartEdgeOffset { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn threshold(s: Span) -> IResult<Span, Threshold> {
    let (s, a) = constant_expression(s)?;
    Ok((s, Threshold { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn timing_check_limit(s: Span) -> IResult<Span, TimingCheckLimit> {
    let (s, a) = expression(s)?;
    Ok((s, TimingCheckLimit { nodes: (a,) }))
}
