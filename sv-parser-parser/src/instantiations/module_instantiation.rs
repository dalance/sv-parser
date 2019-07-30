use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn module_instantiation(s: Span) -> IResult<Span, ModuleInstantiation> {
    let (s, a) = module_identifier(s)?;
    let (s, b) = opt(parameter_value_assignment)(s)?;
    let (s, c) = list(symbol(","), hierarchical_instance)(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        ModuleInstantiation {
            nodes: (a, b, c, d),
        },
    ))
}

#[tracable_parser]
pub(crate) fn parameter_value_assignment(s: Span) -> IResult<Span, ParameterValueAssignment> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = paren(opt(list_of_parameter_assignments))(s)?;
    Ok((s, ParameterValueAssignment { nodes: (a, b) }))
}

#[tracable_parser]
pub(crate) fn list_of_parameter_assignments(s: Span) -> IResult<Span, ListOfParameterAssignments> {
    alt((
        list_of_parameter_assignments_named,
        list_of_parameter_assignments_ordered,
    ))(s)
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn list_of_parameter_assignments_ordered(
    s: Span,
) -> IResult<Span, ListOfParameterAssignments> {
    let (s, a) = list(symbol(","), ordered_parameter_assignment)(s)?;
    Ok((
        s,
        ListOfParameterAssignments::Ordered(Box::new(ListOfParameterAssignmentsOrdered {
            nodes: (a,),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn list_of_parameter_assignments_named(
    s: Span,
) -> IResult<Span, ListOfParameterAssignments> {
    let (s, a) = list(symbol(","), named_parameter_assignment)(s)?;
    Ok((
        s,
        ListOfParameterAssignments::Named(Box::new(ListOfParameterAssignmentsNamed {
            nodes: (a,),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn ordered_parameter_assignment(s: Span) -> IResult<Span, OrderedParameterAssignment> {
    let (s, x) = param_expression(s)?;
    Ok((s, OrderedParameterAssignment { nodes: (x,) }))
}

#[tracable_parser]
pub(crate) fn named_parameter_assignment(s: Span) -> IResult<Span, NamedParameterAssignment> {
    let (s, a) = symbol(".")(s)?;
    let (s, b) = parameter_identifier(s)?;
    let (s, c) = paren(opt(param_expression))(s)?;
    Ok((s, NamedParameterAssignment { nodes: (a, b, c) }))
}

#[tracable_parser]
pub(crate) fn hierarchical_instance(s: Span) -> IResult<Span, HierarchicalInstance> {
    let (s, a) = name_of_instance(s)?;
    let (s, b) = paren(opt(list_of_port_connections))(s)?;
    Ok((s, HierarchicalInstance { nodes: (a, b) }))
}

#[tracable_parser]
pub(crate) fn name_of_instance(s: Span) -> IResult<Span, NameOfInstance> {
    let (s, x) = instance_identifier(s)?;
    let (s, y) = many0(unpacked_dimension)(s)?;
    Ok((s, NameOfInstance { nodes: (x, y) }))
}

#[tracable_parser]
pub(crate) fn list_of_port_connections(s: Span) -> IResult<Span, ListOfPortConnections> {
    alt((
        list_of_port_connections_named,
        list_of_port_connections_ordered,
    ))(s)
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn list_of_port_connections_ordered(s: Span) -> IResult<Span, ListOfPortConnections> {
    let (s, a) = list(symbol(","), ordered_port_connection)(s)?;
    Ok((
        s,
        ListOfPortConnections::Ordered(Box::new(ListOfPortConnectionsOrdered { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn list_of_port_connections_named(s: Span) -> IResult<Span, ListOfPortConnections> {
    let (s, a) = list(symbol(","), named_port_connection)(s)?;
    Ok((
        s,
        ListOfPortConnections::Named(Box::new(ListOfPortConnectionsNamed { nodes: (a,) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn ordered_port_connection(s: Span) -> IResult<Span, OrderedPortConnection> {
    let (s, x) = many0(attribute_instance)(s)?;
    let (s, y) = opt(expression)(s)?;
    Ok((s, OrderedPortConnection { nodes: (x, y) }))
}

#[tracable_parser]
pub(crate) fn named_port_connection(s: Span) -> IResult<Span, NamedPortConnection> {
    alt((
        named_port_connection_identifier,
        named_port_connection_asterisk,
    ))(s)
}

#[tracable_parser]
pub(crate) fn named_port_connection_identifier(s: Span) -> IResult<Span, NamedPortConnection> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = port_identifier(s)?;
    let (s, d) = opt(paren(opt(expression)))(s)?;
    Ok((
        s,
        NamedPortConnection::Identifier(Box::new(NamedPortConnectionIdentifier {
            nodes: (a, b, c, d),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn named_port_connection_asterisk(s: Span) -> IResult<Span, NamedPortConnection> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol(".*")(s)?;
    Ok((
        s,
        NamedPortConnection::Asterisk(Box::new(NamedPortConnectionAsterisk { nodes: (a, b) })),
    ))
}
