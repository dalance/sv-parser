use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn initial_construct(s: Span) -> IResult<Span, InitialConstruct> {
    let (s, a) = keyword("initial")(s)?;
    let (s, b) = statement_or_null(s)?;
    Ok((s, InitialConstruct { nodes: (a, b) }))
}

#[tracable_parser]
pub(crate) fn always_construct(s: Span) -> IResult<Span, AlwaysConstruct> {
    let (s, a) = always_keyword(s)?;
    let (s, b) = statement(s)?;
    Ok((s, AlwaysConstruct { nodes: (a, b) }))
}

#[tracable_parser]
pub(crate) fn always_keyword(s: Span) -> IResult<Span, AlwaysKeyword> {
    alt((
        map(keyword("always_comb"), |x| {
            AlwaysKeyword::AlwaysComb(Box::new(x))
        }),
        map(keyword("always_latch"), |x| {
            AlwaysKeyword::AlwaysLatch(Box::new(x))
        }),
        map(keyword("always_ff"), |x| {
            AlwaysKeyword::AlwaysFf(Box::new(x))
        }),
        map(keyword("always"), |x| AlwaysKeyword::Always(Box::new(x))),
    ))(s)
}

#[tracable_parser]
pub(crate) fn final_construct(s: Span) -> IResult<Span, FinalConstruct> {
    let (s, a) = keyword("final")(s)?;
    let (s, b) = function_statement(s)?;
    Ok((s, FinalConstruct { nodes: (a, b) }))
}

#[tracable_parser]
pub(crate) fn blocking_assignment(s: Span) -> IResult<Span, BlockingAssignment> {
    alt((
        blocking_assignment_variable,
        blocking_assignment_nonrange_variable,
        blocking_assignment_hierarchical_variable,
        map(operator_assignment, |x| {
            BlockingAssignment::OperatorAssignment(Box::new(x))
        }),
    ))(s)
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn blocking_assignment_variable(s: Span) -> IResult<Span, BlockingAssignment> {
    let (s, a) = variable_lvalue(s)?;
    let (s, b) = symbol("=")(s)?;
    let (s, c) = delay_or_event_control(s)?;
    let (s, d) = expression(s)?;
    Ok((
        s,
        BlockingAssignment::Variable(Box::new(BlockingAssignmentVariable {
            nodes: (a, b, c, d),
        })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn blocking_assignment_nonrange_variable(s: Span) -> IResult<Span, BlockingAssignment> {
    let (s, a) = nonrange_variable_lvalue(s)?;
    let (s, b) = symbol("=")(s)?;
    let (s, c) = dynamic_array_new(s)?;
    Ok((
        s,
        BlockingAssignment::NonrangeVariable(Box::new(BlockingAssignmentNonrangeVariable {
            nodes: (a, b, c),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn blocking_assignment_hierarchical_variable(
    s: Span,
) -> IResult<Span, BlockingAssignment> {
    let (s, a) = opt(implicit_class_handle_or_class_scope_or_package_scope)(s)?;
    let (s, b) = hierarchical_variable_identifier(s)?;
    let (s, c) = select(s)?;
    let (s, d) = symbol("=")(s)?;
    let (s, e) = class_new(s)?;
    Ok((
        s,
        BlockingAssignment::HierarchicalVariable(Box::new(
            BlockingAssignmentHierarchicalVariable {
                nodes: (a, b, c, d, e),
            },
        )),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn operator_assignment(s: Span) -> IResult<Span, OperatorAssignment> {
    let (s, a) = variable_lvalue(s)?;
    let (s, b) = assignment_operator(s)?;
    let (s, c) = expression(s)?;
    Ok((s, OperatorAssignment { nodes: (a, b, c) }))
}

#[tracable_parser]
pub(crate) fn assignment_operator(s: Span) -> IResult<Span, AssignmentOperator> {
    alt((
        map(symbol("="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol("+="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol("-="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol("*="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol("/="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol("%="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol("&="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol("|="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol("^="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol("<<<="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol(">>>="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol("<<="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol(">>="), |x| AssignmentOperator { nodes: (x,) }),
    ))(s)
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn nonblocking_assignment(s: Span) -> IResult<Span, NonblockingAssignment> {
    let (s, a) = variable_lvalue(s)?;
    let (s, b) = symbol("<=")(s)?;
    let (s, c) = opt(delay_or_event_control)(s)?;
    let (s, d) = expression(s)?;
    Ok((
        s,
        NonblockingAssignment {
            nodes: (a, b, c, d),
        },
    ))
}

#[tracable_parser]
pub(crate) fn procedural_continuous_assignment(
    s: Span,
) -> IResult<Span, ProceduralContinuousAssignment> {
    alt((
        procedural_continuous_assignment_assign,
        procedural_continuous_assignment_deassign,
        procedural_continuous_assignment_force_variable,
        procedural_continuous_assignment_force_net,
        procedural_continuous_assignment_release_variable,
        procedural_continuous_assignment_release_net,
    ))(s)
}

#[tracable_parser]
pub(crate) fn procedural_continuous_assignment_assign(
    s: Span,
) -> IResult<Span, ProceduralContinuousAssignment> {
    let (s, a) = keyword("assign")(s)?;
    let (s, b) = variable_assignment(s)?;
    Ok((
        s,
        ProceduralContinuousAssignment::Assign(Box::new(ProceduralContinuousAssignmentAssign {
            nodes: (a, b),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn procedural_continuous_assignment_deassign(
    s: Span,
) -> IResult<Span, ProceduralContinuousAssignment> {
    let (s, a) = keyword("deassign")(s)?;
    let (s, b) = variable_lvalue(s)?;
    Ok((
        s,
        ProceduralContinuousAssignment::Deassign(Box::new(
            ProceduralContinuousAssignmentDeassign { nodes: (a, b) },
        )),
    ))
}

#[tracable_parser]
pub(crate) fn procedural_continuous_assignment_force_variable(
    s: Span,
) -> IResult<Span, ProceduralContinuousAssignment> {
    let (s, a) = keyword("force")(s)?;
    let (s, b) = variable_assignment(s)?;
    Ok((
        s,
        ProceduralContinuousAssignment::ForceVariable(Box::new(
            ProceduralContinuousAssignmentForceVariable { nodes: (a, b) },
        )),
    ))
}

#[tracable_parser]
pub(crate) fn procedural_continuous_assignment_force_net(
    s: Span,
) -> IResult<Span, ProceduralContinuousAssignment> {
    let (s, a) = keyword("force")(s)?;
    let (s, b) = net_assignment(s)?;
    Ok((
        s,
        ProceduralContinuousAssignment::ForceNet(Box::new(
            ProceduralContinuousAssignmentForceNet { nodes: (a, b) },
        )),
    ))
}

#[tracable_parser]
pub(crate) fn procedural_continuous_assignment_release_variable(
    s: Span,
) -> IResult<Span, ProceduralContinuousAssignment> {
    let (s, a) = keyword("release")(s)?;
    let (s, b) = variable_lvalue(s)?;
    Ok((
        s,
        ProceduralContinuousAssignment::ReleaseVariable(Box::new(
            ProceduralContinuousAssignmentReleaseVariable { nodes: (a, b) },
        )),
    ))
}

#[tracable_parser]
pub(crate) fn procedural_continuous_assignment_release_net(
    s: Span,
) -> IResult<Span, ProceduralContinuousAssignment> {
    let (s, a) = keyword("release")(s)?;
    let (s, b) = net_lvalue(s)?;
    Ok((
        s,
        ProceduralContinuousAssignment::ReleaseNet(Box::new(
            ProceduralContinuousAssignmentReleaseNet { nodes: (a, b) },
        )),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn variable_assignment(s: Span) -> IResult<Span, VariableAssignment> {
    let (s, a) = variable_lvalue(s)?;
    let (s, b) = symbol("=")(s)?;
    let (s, c) = expression(s)?;
    Ok((s, VariableAssignment { nodes: (a, b, c) }))
}
