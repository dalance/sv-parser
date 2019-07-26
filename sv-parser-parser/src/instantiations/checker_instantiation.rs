use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn checker_instantiation(s: Span) -> IResult<Span, CheckerInstantiation> {
    let (s, a) = ps_checker_identifier(s)?;
    let (s, b) = name_of_instance(s)?;
    let (s, c) = paren(opt(list_of_checker_port_connections))(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        CheckerInstantiation {
            nodes: (a, b, c, d),
        },
    ))
}

#[tracable_parser]
pub(crate) fn list_of_checker_port_connections(
    s: Span,
) -> IResult<Span, ListOfCheckerPortConnections> {
    alt((
        list_of_checker_port_connections_ordered,
        list_of_checker_port_connections_named,
    ))(s)
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn list_of_checker_port_connections_ordered(
    s: Span,
) -> IResult<Span, ListOfCheckerPortConnections> {
    let (s, a) = list(symbol(","), ordered_checker_port_connection)(s)?;
    Ok((
        s,
        ListOfCheckerPortConnections::Ordered(Box::new(ListOfCheckerPortConnectionsOrdered {
            nodes: (a,),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn list_of_checker_port_connections_named(
    s: Span,
) -> IResult<Span, ListOfCheckerPortConnections> {
    let (s, a) = list(symbol(","), named_checker_port_connection)(s)?;
    Ok((
        s,
        ListOfCheckerPortConnections::Named(Box::new(ListOfCheckerPortConnectionsNamed {
            nodes: (a,),
        })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn ordered_checker_port_connection(
    s: Span,
) -> IResult<Span, OrderedCheckerPortConnection> {
    let (s, x) = many0(attribute_instance)(s)?;
    let (s, y) = opt(property_actual_arg)(s)?;
    Ok((s, OrderedCheckerPortConnection { nodes: (x, y) }))
}

#[tracable_parser]
pub(crate) fn named_checker_port_connection(s: Span) -> IResult<Span, NamedCheckerPortConnection> {
    alt((
        named_checker_port_connection_identifier,
        named_checker_port_connection_asterisk,
    ))(s)
}

#[tracable_parser]
pub(crate) fn named_checker_port_connection_identifier(
    s: Span,
) -> IResult<Span, NamedCheckerPortConnection> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = formal_port_identifier(s)?;
    let (s, d) = opt(paren(opt(property_actual_arg)))(s)?;
    Ok((
        s,
        NamedCheckerPortConnection::Identifier(Box::new(NamedCheckerPortConnectionIdentifier {
            nodes: (a, b, c, d),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn named_checker_port_connection_asterisk(
    s: Span,
) -> IResult<Span, NamedCheckerPortConnection> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol(".*")(s)?;
    Ok((
        s,
        NamedCheckerPortConnection::Asterisk(Box::new(NamedCheckerPortConnectionAsterisk {
            nodes: (a, b),
        })),
    ))
}
