use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn defparam_assignment(s: Span) -> IResult<Span, DefparamAssignment> {
    let (s, a) = hierarchical_parameter_identifier(s)?;
    let (s, b) = symbol("=")(s)?;
    let (s, c) = constant_mintypmax_expression(s)?;
    Ok((s, DefparamAssignment { nodes: (a, b, c) }))
}

#[tracable_parser]
pub(crate) fn net_decl_assignment(s: Span) -> IResult<Span, NetDeclAssignment> {
    let (s, a) = net_identifier(s)?;
    let (s, b) = many0(unpacked_dimension)(s)?;
    let (s, c) = opt(pair(symbol("="), expression))(s)?;
    Ok((s, NetDeclAssignment { nodes: (a, b, c) }))
}

#[tracable_parser]
pub(crate) fn param_assignment(s: Span) -> IResult<Span, ParamAssignment> {
    let (s, a) = parameter_identifier(s)?;
    let (s, b) = many0(unpacked_dimension)(s)?;
    let (s, c) = opt(pair(symbol("="), constant_param_expression))(s)?;
    Ok((s, ParamAssignment { nodes: (a, b, c) }))
}

#[tracable_parser]
pub(crate) fn specparam_assignment(s: Span) -> IResult<Span, SpecparamAssignment> {
    alt((
        specparam_assignment_mintypmax,
        map(pulse_control_specparam, |x| {
            SpecparamAssignment::PulseControlSpecparam(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn specparam_assignment_mintypmax(s: Span) -> IResult<Span, SpecparamAssignment> {
    let (s, a) = specparam_identifier(s)?;
    let (s, b) = symbol("=")(s)?;
    let (s, c) = constant_mintypmax_expression(s)?;
    Ok((
        s,
        SpecparamAssignment::Mintypmax(Box::new(SpecparamAssignmentMintypmax { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn type_assignment(s: Span) -> IResult<Span, TypeAssignment> {
    let (s, a) = type_identifier(s)?;
    let (s, b) = opt(pair(symbol("="), data_type))(s)?;
    Ok((s, TypeAssignment { nodes: (a, b) }))
}

#[tracable_parser]
pub(crate) fn pulse_control_specparam(s: Span) -> IResult<Span, PulseControlSpecparam> {
    alt((
        pulse_control_specparam_without_descriptor,
        pulse_control_specparam_with_descriptor,
    ))(s)
}

#[tracable_parser]
pub(crate) fn pulse_control_specparam_without_descriptor(
    s: Span,
) -> IResult<Span, PulseControlSpecparam> {
    let (s, a) = symbol("PATHPULSE$")(s)?;
    let (s, b) = symbol("=")(s)?;
    let (s, c) = paren(pair(
        reject_limit_value,
        opt(pair(symbol(","), error_limit_value)),
    ))(s)?;
    Ok((
        s,
        PulseControlSpecparam::WithoutDescriptor(Box::new(
            PulseControlSpecparamWithoutDescriptor { nodes: (a, b, c) },
        )),
    ))
}

#[tracable_parser]
pub(crate) fn pulse_control_specparam_with_descriptor(
    s: Span,
) -> IResult<Span, PulseControlSpecparam> {
    let (s, a) = symbol("PATHPULSE$")(s)?;
    let (s, b) = specify_input_terminal_descriptor(s)?;
    let (s, c) = symbol("$")(s)?;
    let (s, d) = specify_output_terminal_descriptor(s)?;
    let (s, e) = symbol("=")(s)?;
    let (s, f) = paren(pair(
        reject_limit_value,
        opt(pair(symbol(","), error_limit_value)),
    ))(s)?;
    Ok((
        s,
        PulseControlSpecparam::WithDescriptor(Box::new(PulseControlSpecparamWithDescriptor {
            nodes: (a, b, c, d, e, f),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn error_limit_value(s: Span) -> IResult<Span, ErrorLimitValue> {
    let (s, a) = limit_value(s)?;
    Ok((s, ErrorLimitValue { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn reject_limit_value(s: Span) -> IResult<Span, RejectLimitValue> {
    let (s, a) = limit_value(s)?;
    Ok((s, RejectLimitValue { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn limit_value(s: Span) -> IResult<Span, LimitValue> {
    let (s, a) = constant_mintypmax_expression(s)?;
    Ok((s, LimitValue { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn variable_decl_assignment(s: Span) -> IResult<Span, VariableDeclAssignment> {
    alt((
        variable_decl_assignment_dynamic_array,
        variable_decl_assignment_class,
        variable_decl_assignment_variable,
    ))(s)
}

#[tracable_parser]
pub(crate) fn variable_decl_assignment_variable(s: Span) -> IResult<Span, VariableDeclAssignment> {
    let (s, a) = variable_identifier(s)?;
    let (s, b) = many0(variable_dimension)(s)?;
    let (s, c) = opt(pair(symbol("="), expression))(s)?;
    Ok((
        s,
        VariableDeclAssignment::Variable(Box::new(VariableDeclAssignmentVariable {
            nodes: (a, b, c),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn variable_decl_assignment_dynamic_array(
    s: Span,
) -> IResult<Span, VariableDeclAssignment> {
    let (s, a) = dynamic_array_variable_identifier(s)?;
    let (s, b) = unsized_dimension(s)?;
    let (s, c) = many0(variable_dimension)(s)?;
    let (s, d) = opt(pair(symbol("="), dynamic_array_new))(s)?;
    Ok((
        s,
        VariableDeclAssignment::DynamicArray(Box::new(VariableDeclAssignmentDynamicArray {
            nodes: (a, b, c, d),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn variable_decl_assignment_class(s: Span) -> IResult<Span, VariableDeclAssignment> {
    let (s, a) = class_variable_identifier(s)?;
    let (s, b) = pair(symbol("="), class_new)(s)?;
    Ok((
        s,
        VariableDeclAssignment::Class(Box::new(VariableDeclAssignmentClass { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn class_new(s: Span) -> IResult<Span, ClassNew> {
    alt((class_new_expression, class_new_argument))(s)
}

#[tracable_parser]
pub(crate) fn class_new_argument(s: Span) -> IResult<Span, ClassNew> {
    let (s, a) = opt(class_scope)(s)?;
    let (s, b) = keyword("new")(s)?;
    let (s, c) = opt(paren(list_of_arguments))(s)?;
    Ok((
        s,
        ClassNew::Argument(Box::new(ClassNewArgument { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn class_new_expression(s: Span) -> IResult<Span, ClassNew> {
    let (s, a) = keyword("new")(s)?;
    let (s, b) = expression(s)?;
    Ok((
        s,
        ClassNew::Expression(Box::new(ClassNewExpression { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn dynamic_array_new(s: Span) -> IResult<Span, DynamicArrayNew> {
    let (s, a) = keyword("new")(s)?;
    let (s, b) = bracket(expression)(s)?;
    let (s, c) = opt(paren(expression))(s)?;
    Ok((s, DynamicArrayNew { nodes: (a, b, c) }))
}
