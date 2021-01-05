use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clocking_declaration(s: Span) -> IResult<Span, ClockingDeclaration> {
    alt((clocking_declaration_local, clocking_declaration_global))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clocking_declaration_local(s: Span) -> IResult<Span, ClockingDeclaration> {
    let (s, a) = opt(default)(s)?;
    let (s, b) = keyword("clocking")(s)?;
    let (s, c) = opt(clocking_identifier)(s)?;
    let (s, d) = clocking_event(s)?;
    let (s, e) = symbol(";")(s)?;
    let (s, (f, g)) = many_till(clocking_item, keyword("endclocking"))(s)?;
    let (s, h) = opt(pair(symbol(":"), clocking_identifier))(s)?;
    Ok((
        s,
        ClockingDeclaration::Local(Box::new(ClockingDeclarationLocal {
            nodes: (a, b, c, d, e, f, g, h),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn default(s: Span) -> IResult<Span, Default> {
    let (s, a) = keyword("default")(s)?;
    Ok((s, Default { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clocking_declaration_global(s: Span) -> IResult<Span, ClockingDeclaration> {
    let (s, a) = keyword("global")(s)?;
    let (s, b) = keyword("clocking")(s)?;
    let (s, c) = opt(clocking_identifier)(s)?;
    let (s, d) = clocking_event(s)?;
    let (s, e) = symbol(";")(s)?;
    let (s, f) = keyword("endclocking")(s)?;
    let (s, g) = opt(pair(symbol(":"), clocking_identifier))(s)?;
    Ok((
        s,
        ClockingDeclaration::Global(Box::new(ClockingDeclarationGlobal {
            nodes: (a, b, c, d, e, f, g),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clocking_event(s: Span) -> IResult<Span, ClockingEvent> {
    alt((clocking_event_identifier, clocking_event_expression))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clocking_event_identifier(s: Span) -> IResult<Span, ClockingEvent> {
    let (s, a) = symbol("@")(s)?;
    let (s, b) = identifier(s)?;
    Ok((
        s,
        ClockingEvent::Identifier(Box::new(ClockingEventIdentifier { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clocking_event_expression(s: Span) -> IResult<Span, ClockingEvent> {
    let (s, a) = symbol("@")(s)?;
    let (s, b) = paren(event_expression)(s)?;
    Ok((
        s,
        ClockingEvent::Expression(Box::new(ClockingEventExpression { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clocking_item(s: Span) -> IResult<Span, ClockingItem> {
    alt((
        clocking_item_default,
        clocking_item_direction,
        clocking_item_assertion,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clocking_item_default(s: Span) -> IResult<Span, ClockingItem> {
    let (s, a) = keyword("default")(s)?;
    let (s, b) = default_skew(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ClockingItem::Default(Box::new(ClockingItemDefault { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clocking_item_direction(s: Span) -> IResult<Span, ClockingItem> {
    let (s, a) = clocking_direction(s)?;
    let (s, b) = list_of_clocking_decl_assign(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ClockingItem::Direction(Box::new(ClockingItemDirection { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clocking_item_assertion(s: Span) -> IResult<Span, ClockingItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = assertion_item_declaration(s)?;
    Ok((
        s,
        ClockingItem::Assertion(Box::new(ClockingItemAssertion { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn default_skew(s: Span) -> IResult<Span, DefaultSkew> {
    alt((
        default_skew_input_output,
        default_skew_input,
        default_skew_output,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn default_skew_input(s: Span) -> IResult<Span, DefaultSkew> {
    let (s, a) = keyword("input")(s)?;
    let (s, b) = clocking_skew(s)?;
    Ok((
        s,
        DefaultSkew::Input(Box::new(DefaultSkewInput { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn default_skew_output(s: Span) -> IResult<Span, DefaultSkew> {
    let (s, a) = keyword("output")(s)?;
    let (s, b) = clocking_skew(s)?;
    Ok((
        s,
        DefaultSkew::Output(Box::new(DefaultSkewOutput { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn default_skew_input_output(s: Span) -> IResult<Span, DefaultSkew> {
    let (s, a) = keyword("input")(s)?;
    let (s, b) = clocking_skew(s)?;
    let (s, c) = keyword("output")(s)?;
    let (s, d) = clocking_skew(s)?;
    Ok((
        s,
        DefaultSkew::InputOutput(Box::new(DefaultSkewInputOutput {
            nodes: (a, b, c, d),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clocking_direction(s: Span) -> IResult<Span, ClockingDirection> {
    alt((
        clocking_direction_input_output,
        clocking_direction_input,
        clocking_direction_output,
        clocking_direction_inout,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clocking_direction_input(s: Span) -> IResult<Span, ClockingDirection> {
    let (s, a) = keyword("input")(s)?;
    let (s, b) = opt(clocking_skew)(s)?;
    Ok((
        s,
        ClockingDirection::Input(Box::new(ClockingDirectionInput { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clocking_direction_output(s: Span) -> IResult<Span, ClockingDirection> {
    let (s, a) = keyword("output")(s)?;
    let (s, b) = opt(clocking_skew)(s)?;
    Ok((
        s,
        ClockingDirection::Output(Box::new(ClockingDirectionOutput { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clocking_direction_input_output(s: Span) -> IResult<Span, ClockingDirection> {
    let (s, a) = keyword("input")(s)?;
    let (s, b) = opt(clocking_skew)(s)?;
    let (s, c) = keyword("output")(s)?;
    let (s, d) = opt(clocking_skew)(s)?;
    Ok((
        s,
        ClockingDirection::InputOutput(Box::new(ClockingDirectionInputOutput {
            nodes: (a, b, c, d),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clocking_direction_inout(s: Span) -> IResult<Span, ClockingDirection> {
    let (s, a) = keyword("inout")(s)?;
    Ok((s, ClockingDirection::Inout(Box::new(a))))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn list_of_clocking_decl_assign(s: Span) -> IResult<Span, ListOfClockingDeclAssign> {
    let (s, a) = list(symbol(","), clocking_decl_assign)(s)?;
    Ok((s, ListOfClockingDeclAssign { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clocking_decl_assign(s: Span) -> IResult<Span, ClockingDeclAssign> {
    let (s, a) = signal_identifier(s)?;
    let (s, b) = opt(pair(symbol("="), expression))(s)?;
    Ok((s, ClockingDeclAssign { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clocking_skew(s: Span) -> IResult<Span, ClockingSkew> {
    alt((
        clocking_skew_edge,
        map(delay_control, |x| ClockingSkew::DelayControl(Box::new(x))),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clocking_skew_edge(s: Span) -> IResult<Span, ClockingSkew> {
    let (s, a) = edge_identifier(s)?;
    let (s, b) = opt(delay_control)(s)?;
    Ok((
        s,
        ClockingSkew::Edge(Box::new(ClockingSkewEdge { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clocking_drive(s: Span) -> IResult<Span, ClockingDrive> {
    let (s, a) = clockvar_expression(s)?;
    let (s, b) = symbol("<=")(s)?;
    let (s, c) = opt(cycle_delay)(s)?;
    let (s, d) = expression(s)?;
    Ok((
        s,
        ClockingDrive {
            nodes: (a, b, c, d),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn cycle_delay(s: Span) -> IResult<Span, CycleDelay> {
    alt((
        cycle_delay_integral,
        cycle_delay_identifier,
        cycle_delay_expression,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn cycle_delay_integral(s: Span) -> IResult<Span, CycleDelay> {
    let (s, a) = symbol("##")(s)?;
    let (s, b) = integral_number(s)?;
    Ok((
        s,
        CycleDelay::Integral(Box::new(CycleDelayIntegral { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn cycle_delay_identifier(s: Span) -> IResult<Span, CycleDelay> {
    let (s, a) = symbol("##")(s)?;
    let (s, b) = identifier(s)?;
    Ok((
        s,
        CycleDelay::Identifier(Box::new(CycleDelayIdentifier { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn cycle_delay_expression(s: Span) -> IResult<Span, CycleDelay> {
    let (s, a) = symbol("##")(s)?;
    let (s, b) = paren(expression)(s)?;
    Ok((
        s,
        CycleDelay::Expression(Box::new(CycleDelayExpression { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clockvar(s: Span) -> IResult<Span, Clockvar> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, Clockvar { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn clockvar_expression(s: Span) -> IResult<Span, ClockvarExpression> {
    let (s, a) = clockvar(s)?;
    let (s, b) = select(s)?;
    Ok((s, ClockvarExpression { nodes: (a, b) }))
}
