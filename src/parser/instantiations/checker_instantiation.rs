use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct CheckerInstantiation<'a> {
    pub nodes: (
        PsCheckerIdentifier<'a>,
        NameOfInstance<'a>,
        Option<ListOfCheckerPortConnections<'a>>,
    ),
}

#[derive(Debug)]
pub enum ListOfCheckerPortConnections<'a> {
    Ordered(Vec<OrderedCheckerPortConnection<'a>>),
    Named(Vec<NamedCheckerPortConnection<'a>>),
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
        FormalPortIdentifier<'a>,
        Option<PropertyActualArg<'a>>,
    ),
}

#[derive(Debug)]
pub struct NamedCheckerPortConnectionAsterisk<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>,),
}

// -----------------------------------------------------------------------------

pub fn checker_instantiation(s: &str) -> IResult<&str, CheckerInstantiation> {
    let (s, x) = ps_checker_identifier(s)?;
    let (s, y) = name_of_instance(s)?;
    let (s, z) = paren(opt(list_of_checker_port_connections))(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, CheckerInstantiation { nodes: (x, y, z) }))
}

pub fn list_of_checker_port_connections(s: &str) -> IResult<&str, ListOfCheckerPortConnections> {
    alt((
        map(
            separated_nonempty_list(symbol(","), ordered_checker_port_connection),
            |x| ListOfCheckerPortConnections::Ordered(x),
        ),
        map(
            separated_nonempty_list(symbol(","), named_checker_port_connection),
            |x| ListOfCheckerPortConnections::Named(x),
        ),
    ))(s)
}

pub fn ordered_checker_port_connection(s: &str) -> IResult<&str, OrderedCheckerPortConnection> {
    let (s, x) = many0(attribute_instance)(s)?;
    let (s, y) = opt(property_actual_arg)(s)?;
    Ok((s, OrderedCheckerPortConnection { nodes: (x, y) }))
}

pub fn named_checker_port_connection(s: &str) -> IResult<&str, NamedCheckerPortConnection> {
    alt((
        named_checker_port_connection_identifier,
        named_checker_port_connection_asterisk,
    ))(s)
}

pub fn named_checker_port_connection_identifier(
    s: &str,
) -> IResult<&str, NamedCheckerPortConnection> {
    let (s, x) = many0(attribute_instance)(s)?;
    let (s, _) = symbol(".")(s)?;
    let (s, y) = formal_port_identifier(s)?;
    let (s, z) = opt(paren(opt(property_actual_arg)))(s)?;
    let z = if let Some(Some(z)) = z { Some(z) } else { None };
    Ok((
        s,
        NamedCheckerPortConnection::Identifier(NamedCheckerPortConnectionIdentifier {
            nodes: (x, y, z),
        }),
    ))
}

pub fn named_checker_port_connection_asterisk(
    s: &str,
) -> IResult<&str, NamedCheckerPortConnection> {
    let (s, x) = many0(attribute_instance)(s)?;
    let (s, _) = symbol(".")(s)?;
    let (s, _) = symbol("*")(s)?;
    Ok((
        s,
        NamedCheckerPortConnection::Asterisk(NamedCheckerPortConnectionAsterisk { nodes: (x,) }),
    ))
}

// -----------------------------------------------------------------------------
