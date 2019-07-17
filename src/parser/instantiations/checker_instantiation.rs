use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct CheckerInstantiation<'a> {
    pub nodes: (
        PsCheckerIdentifier<'a>,
        NameOfInstance<'a>,
        Paren<'a, Option<ListOfCheckerPortConnections<'a>>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum ListOfCheckerPortConnections<'a> {
    Ordered(ListOfCheckerPortConnectionsOrdered<'a>),
    Named(ListOfCheckerPortConnectionsNamed<'a>),
}

#[derive(Debug, Node)]
pub struct ListOfCheckerPortConnectionsOrdered<'a> {
    pub nodes: (List<Symbol<'a>, OrderedCheckerPortConnection<'a>>,),
}

#[derive(Debug, Node)]
pub struct ListOfCheckerPortConnectionsNamed<'a> {
    pub nodes: (List<Symbol<'a>, NamedCheckerPortConnection<'a>>,),
}

#[derive(Debug, Node)]
pub struct OrderedCheckerPortConnection<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, Option<PropertyActualArg<'a>>),
}

#[derive(Debug, Node)]
pub enum NamedCheckerPortConnection<'a> {
    Identifier(NamedCheckerPortConnectionIdentifier<'a>),
    Asterisk(NamedCheckerPortConnectionAsterisk<'a>),
}

#[derive(Debug, Node)]
pub struct NamedCheckerPortConnectionIdentifier<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Symbol<'a>,
        FormalPortIdentifier<'a>,
        Option<Paren<'a, Option<PropertyActualArg<'a>>>>,
    ),
}

#[derive(Debug, Node)]
pub struct NamedCheckerPortConnectionAsterisk<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, Symbol<'a>),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn checker_instantiation(s: Span) -> IResult<Span, CheckerInstantiation> {
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

#[parser]
pub fn list_of_checker_port_connections(s: Span) -> IResult<Span, ListOfCheckerPortConnections> {
    alt((
        list_of_checker_port_connections_ordered,
        list_of_checker_port_connections_named,
    ))(s)
}

#[parser]
pub fn list_of_checker_port_connections_ordered(
    s: Span,
) -> IResult<Span, ListOfCheckerPortConnections> {
    let (s, a) = list(symbol(","), ordered_checker_port_connection)(s)?;
    Ok((
        s,
        ListOfCheckerPortConnections::Ordered(ListOfCheckerPortConnectionsOrdered { nodes: (a,) }),
    ))
}

#[parser]
pub fn list_of_checker_port_connections_named(
    s: Span,
) -> IResult<Span, ListOfCheckerPortConnections> {
    let (s, a) = list(symbol(","), named_checker_port_connection)(s)?;
    Ok((
        s,
        ListOfCheckerPortConnections::Named(ListOfCheckerPortConnectionsNamed { nodes: (a,) }),
    ))
}

#[parser]
pub fn ordered_checker_port_connection(s: Span) -> IResult<Span, OrderedCheckerPortConnection> {
    let (s, x) = many0(attribute_instance)(s)?;
    let (s, y) = opt(property_actual_arg)(s)?;
    Ok((s, OrderedCheckerPortConnection { nodes: (x, y) }))
}

#[parser]
pub fn named_checker_port_connection(s: Span) -> IResult<Span, NamedCheckerPortConnection> {
    alt((
        named_checker_port_connection_identifier,
        named_checker_port_connection_asterisk,
    ))(s)
}

#[parser]
pub fn named_checker_port_connection_identifier(
    s: Span,
) -> IResult<Span, NamedCheckerPortConnection> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = formal_port_identifier(s)?;
    let (s, d) = opt(paren(opt(property_actual_arg)))(s)?;
    Ok((
        s,
        NamedCheckerPortConnection::Identifier(NamedCheckerPortConnectionIdentifier {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn named_checker_port_connection_asterisk(
    s: Span,
) -> IResult<Span, NamedCheckerPortConnection> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol(".*")(s)?;
    Ok((
        s,
        NamedCheckerPortConnection::Asterisk(NamedCheckerPortConnectionAsterisk { nodes: (a, b) }),
    ))
}

// -----------------------------------------------------------------------------
