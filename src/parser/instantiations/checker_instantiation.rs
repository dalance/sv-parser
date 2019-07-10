use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct CheckerInstantiation<'a> {
    pub nodes: (
        PsCheckerIdentifier<'a>,
        NameOfInstance<'a>,
        Symbol<'a>,
        Option<ListOfCheckerPortConnections<'a>>,
        Symbol<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug)]
pub enum ListOfCheckerPortConnections<'a> {
    Ordered(ListOfCheckerPortConnectionsOrdered<'a>),
    Named(ListOfCheckerPortConnectionsNamed<'a>),
}

#[derive(Debug)]
pub struct ListOfCheckerPortConnectionsOrdered<'a> {
    pub nodes: (
        OrderedCheckerPortConnection<'a>,
        Vec<(Symbol<'a>, OrderedCheckerPortConnection<'a>)>,
    ),
}

#[derive(Debug)]
pub struct ListOfCheckerPortConnectionsNamed<'a> {
    pub nodes: (
        NamedCheckerPortConnection<'a>,
        Vec<(Symbol<'a>, NamedCheckerPortConnection<'a>)>,
    ),
}

#[derive(Debug)]
pub struct OrderedCheckerPortConnection<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, Option<PropertyActualArg<'a>>),
}

#[derive(Debug)]
pub enum NamedCheckerPortConnection<'a> {
    Identifier(NamedCheckerPortConnectionIdentifier<'a>),
    Asterisk(NamedCheckerPortConnectionAsterisk<'a>),
}

#[derive(Debug)]
pub struct NamedCheckerPortConnectionIdentifier<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Symbol<'a>,
        FormalPortIdentifier<'a>,
        Option<(Symbol<'a>, Option<PropertyActualArg<'a>>, Symbol<'a>)>,
    ),
}

#[derive(Debug)]
pub struct NamedCheckerPortConnectionAsterisk<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, Symbol<'a>),
}

// -----------------------------------------------------------------------------

pub fn checker_instantiation(s: Span) -> IResult<Span, CheckerInstantiation> {
    let (s, a) = ps_checker_identifier(s)?;
    let (s, b) = name_of_instance(s)?;
    let (s, (c, d, e)) = paren2(opt(list_of_checker_port_connections))(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        CheckerInstantiation {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

pub fn list_of_checker_port_connections(s: Span) -> IResult<Span, ListOfCheckerPortConnections> {
    alt((
        list_of_checker_port_connections_ordered,
        list_of_checker_port_connections_named,
    ))(s)
}

pub fn list_of_checker_port_connections_ordered(
    s: Span,
) -> IResult<Span, ListOfCheckerPortConnections> {
    let (s, a) = ordered_checker_port_connection(s)?;
    let (s, b) = many0(pair(symbol(","), ordered_checker_port_connection))(s)?;
    Ok((
        s,
        ListOfCheckerPortConnections::Ordered(ListOfCheckerPortConnectionsOrdered {
            nodes: (a, b),
        }),
    ))
}

pub fn list_of_checker_port_connections_named(
    s: Span,
) -> IResult<Span, ListOfCheckerPortConnections> {
    let (s, a) = named_checker_port_connection(s)?;
    let (s, b) = many0(pair(symbol(","), named_checker_port_connection))(s)?;
    Ok((
        s,
        ListOfCheckerPortConnections::Named(ListOfCheckerPortConnectionsNamed { nodes: (a, b) }),
    ))
}

pub fn ordered_checker_port_connection(s: Span) -> IResult<Span, OrderedCheckerPortConnection> {
    let (s, x) = many0(attribute_instance)(s)?;
    let (s, y) = opt(property_actual_arg)(s)?;
    Ok((s, OrderedCheckerPortConnection { nodes: (x, y) }))
}

pub fn named_checker_port_connection(s: Span) -> IResult<Span, NamedCheckerPortConnection> {
    alt((
        named_checker_port_connection_identifier,
        named_checker_port_connection_asterisk,
    ))(s)
}

pub fn named_checker_port_connection_identifier(
    s: Span,
) -> IResult<Span, NamedCheckerPortConnection> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = formal_port_identifier(s)?;
    let (s, d) = opt(paren2(opt(property_actual_arg)))(s)?;
    Ok((
        s,
        NamedCheckerPortConnection::Identifier(NamedCheckerPortConnectionIdentifier {
            nodes: (a, b, c, d),
        }),
    ))
}

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
