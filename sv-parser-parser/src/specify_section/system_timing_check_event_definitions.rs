use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn timing_check_event(s: Span) -> IResult<Span, TimingCheckEvent> {
    let (s, a) = opt(timing_check_event_control)(s)?;
    let (s, b) = specify_terminal_descriptor(s)?;
    let (s, c) = opt(pair(symbol("&&&"), timing_check_condition))(s)?;
    Ok((s, TimingCheckEvent { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn controlled_timing_check_event(s: Span) -> IResult<Span, ControlledTimingCheckEvent> {
    let (s, a) = timing_check_event_control(s)?;
    let (s, b) = specify_terminal_descriptor(s)?;
    let (s, c) = opt(pair(symbol("&&&"), timing_check_condition))(s)?;
    Ok((s, ControlledTimingCheckEvent { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn timing_check_event_control(s: Span) -> IResult<Span, TimingCheckEventControl> {
    alt((
        map(keyword("posedge"), |x| {
            TimingCheckEventControl::Posedge(Box::new(x))
        }),
        map(keyword("negedge"), |x| {
            TimingCheckEventControl::Negedge(Box::new(x))
        }),
        map(keyword("edge"), |x| {
            TimingCheckEventControl::Edge(Box::new(x))
        }),
        map(edge_control_specifier, |x| {
            TimingCheckEventControl::EdgeControlSpecifier(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn specify_terminal_descriptor(s: Span) -> IResult<Span, SpecifyTerminalDescriptor> {
    alt((
        map(specify_input_terminal_descriptor, |x| {
            SpecifyTerminalDescriptor::SpecifyInputTerminalDescriptor(Box::new(x))
        }),
        map(specify_output_terminal_descriptor, |x| {
            SpecifyTerminalDescriptor::SpecifyOutputTerminalDescriptor(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn edge_control_specifier(s: Span) -> IResult<Span, EdgeControlSpecifier> {
    let (s, a) = keyword("edge")(s)?;
    let (s, b) = bracket(list(symbol(","), edge_descriptor))(s)?;
    Ok((s, EdgeControlSpecifier { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn edge_descriptor(s: Span) -> IResult<Span, EdgeDescriptor> {
    alt((
        map(keyword("01"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("10"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("x0"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("x1"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("X0"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("X1"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("z0"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("z1"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("Z0"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("Z1"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("0x"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("1x"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("0X"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("1X"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("0z"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("1z"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("0Z"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("1Z"), |x| EdgeDescriptor { nodes: (x,) }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn timing_check_condition(s: Span) -> IResult<Span, TimingCheckCondition> {
    alt((
        map(scalar_timing_check_condition, |x| {
            TimingCheckCondition::ScalarTimingCheckCondition(Box::new(x))
        }),
        timing_check_condition_paren,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn timing_check_condition_paren(s: Span) -> IResult<Span, TimingCheckCondition> {
    let (s, a) = paren(scalar_timing_check_condition)(s)?;
    Ok((
        s,
        TimingCheckCondition::Paren(Box::new(TimingCheckConditionParen { nodes: (a,) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn scalar_timing_check_condition(s: Span) -> IResult<Span, ScalarTimingCheckCondition> {
    alt((
        map(expression, |x| {
            ScalarTimingCheckCondition::Expression(Box::new(x))
        }),
        scalar_timing_check_condition_unary,
        scalar_timing_check_condition_binary,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn scalar_timing_check_condition_unary(
    s: Span,
) -> IResult<Span, ScalarTimingCheckCondition> {
    let (s, a) = symbol("~")(s)?;
    let (s, b) = expression(s)?;
    Ok((
        s,
        ScalarTimingCheckCondition::Unary(Box::new(ScalarTimingCheckConditionUnary {
            nodes: (a, b),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn scalar_timing_check_condition_binary(
    s: Span,
) -> IResult<Span, ScalarTimingCheckCondition> {
    let (s, a) = expression(s)?;
    let (s, b) = alt((symbol("==="), symbol("=="), symbol("!=="), symbol("!=")))(s)?;
    let (s, c) = scalar_constant(s)?;
    Ok((
        s,
        ScalarTimingCheckCondition::Binary(Box::new(ScalarTimingCheckConditionBinary {
            nodes: (a, b, c),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn scalar_constant(s: Span) -> IResult<Span, ScalarConstant> {
    alt((
        map(keyword("1'b0"), |x| ScalarConstant { nodes: (x,) }),
        map(keyword("1'b1"), |x| ScalarConstant { nodes: (x,) }),
        map(keyword("1'B0"), |x| ScalarConstant { nodes: (x,) }),
        map(keyword("1'B1"), |x| ScalarConstant { nodes: (x,) }),
        map(keyword("'b0"), |x| ScalarConstant { nodes: (x,) }),
        map(keyword("'b1"), |x| ScalarConstant { nodes: (x,) }),
        map(keyword("'B0"), |x| ScalarConstant { nodes: (x,) }),
        map(keyword("'B1"), |x| ScalarConstant { nodes: (x,) }),
        map(keyword("1"), |x| ScalarConstant { nodes: (x,) }),
        map(keyword("0"), |x| ScalarConstant { nodes: (x,) }),
    ))(s)
}
