use crate::*;

// -----------------------------------------------------------------------------

#[packrat_parser]
#[parser]
pub(crate) fn net_lvalue(s: Span) -> IResult<Span, NetLvalue> {
    alt((net_lvalue_identifier, net_lvalue_lvalue, net_lvalue_pattern))(s)
}

#[parser]
pub(crate) fn net_lvalue_identifier(s: Span) -> IResult<Span, NetLvalue> {
    let (s, a) = ps_or_hierarchical_net_identifier(s)?;
    let (s, b) = constant_select(s)?;
    Ok((
        s,
        NetLvalue::Identifier(Box::new(NetLvalueIdentifier { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn net_lvalue_pattern(s: Span) -> IResult<Span, NetLvalue> {
    let (s, a) = opt(assignment_pattern_expression_type)(s)?;
    let (s, b) = assignment_pattern_net_lvalue(s)?;
    Ok((
        s,
        NetLvalue::Pattern(Box::new(NetLvaluePattern { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn net_lvalue_lvalue(s: Span) -> IResult<Span, NetLvalue> {
    let (s, a) = brace(list(symbol(","), net_lvalue))(s)?;
    Ok((
        s,
        NetLvalue::Lvalue(Box::new(NetLvalueLvalue { nodes: (a,) })),
    ))
}

#[packrat_parser]
#[parser]
pub(crate) fn variable_lvalue(s: Span) -> IResult<Span, VariableLvalue> {
    alt((
        variable_lvalue_identifier,
        variable_lvalue_lvalue,
        variable_lvalue_pattern,
        map(streaming_concatenation, |x| {
            VariableLvalue::StreamingConcatenation(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn variable_lvalue_identifier(s: Span) -> IResult<Span, VariableLvalue> {
    let (s, a) = opt(implicit_class_handle_or_package_scope)(s)?;
    let (s, b) = hierarchical_variable_identifier(s)?;
    let (s, c) = select(s)?;
    Ok((
        s,
        VariableLvalue::Identifier(Box::new(VariableLvalueIdentifier { nodes: (a, b, c) })),
    ))
}

#[parser]
pub(crate) fn variable_lvalue_pattern(s: Span) -> IResult<Span, VariableLvalue> {
    let (s, a) = opt(assignment_pattern_expression_type)(s)?;
    let (s, b) = assignment_pattern_variable_lvalue(s)?;
    Ok((
        s,
        VariableLvalue::Pattern(Box::new(VariableLvaluePattern { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn variable_lvalue_lvalue(s: Span) -> IResult<Span, VariableLvalue> {
    let (s, a) = brace(list(symbol(","), variable_lvalue))(s)?;
    Ok((
        s,
        VariableLvalue::Lvalue(Box::new(VariableLvalueLvalue { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn nonrange_variable_lvalue(s: Span) -> IResult<Span, NonrangeVariableLvalue> {
    let (s, a) = opt(implicit_class_handle_or_package_scope)(s)?;
    let (s, b) = hierarchical_variable_identifier(s)?;
    let (s, c) = nonrange_select(s)?;
    Ok((s, NonrangeVariableLvalue { nodes: (a, b, c) }))
}
