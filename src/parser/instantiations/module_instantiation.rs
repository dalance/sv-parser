use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct ModuleInstantiation<'a> {
    pub nodes: (
        ModuleIdentifier<'a>,
        Option<ParameterValueAssignment<'a>>,
        HierarchicalInstance<'a>,
        Vec<(Symbol<'a>, HierarchicalInstance<'a>)>,
        Symbol<'a>,
    ),
}

#[derive(Debug)]
pub struct ParameterValueAssignment<'a> {
    pub nodes: (
        Symbol<'a>,
        (
            Symbol<'a>,
            Option<ListOfParameterAssignments<'a>>,
            Symbol<'a>,
        ),
    ),
}

#[derive(Debug)]
pub enum ListOfParameterAssignments<'a> {
    Ordered(ListOfParameterAssignmentsOrdered<'a>),
    Named(ListOfParameterAssignmentsNamed<'a>),
}

#[derive(Debug)]
pub struct ListOfParameterAssignmentsOrdered<'a> {
    pub nodes: (
        OrderedParameterAssignment<'a>,
        Vec<(Symbol<'a>, OrderedParameterAssignment<'a>)>,
    ),
}

#[derive(Debug)]
pub struct ListOfParameterAssignmentsNamed<'a> {
    pub nodes: (
        NamedParameterAssignment<'a>,
        Vec<(Symbol<'a>, NamedParameterAssignment<'a>)>,
    ),
}

#[derive(Debug)]
pub struct OrderedParameterAssignment<'a> {
    pub nodes: (ParamExpression<'a>,),
}

#[derive(Debug)]
pub struct NamedParameterAssignment<'a> {
    pub nodes: (
        Symbol<'a>,
        ParameterIdentifier<'a>,
        (Symbol<'a>, Option<ParamExpression<'a>>, Symbol<'a>),
    ),
}

#[derive(Debug)]
pub struct HierarchicalInstance<'a> {
    pub nodes: (
        NameOfInstance<'a>,
        (Symbol<'a>, Option<ListOfPortConnections<'a>>, Symbol<'a>),
    ),
}

#[derive(Debug)]
pub struct NameOfInstance<'a> {
    pub nodes: (InstanceIdentifier<'a>, Vec<UnpackedDimension<'a>>),
}

#[derive(Debug)]
pub enum ListOfPortConnections<'a> {
    Ordered(ListOfPortConnectionsOrdered<'a>),
    Named(ListOfPortConnectionsNamed<'a>),
}

#[derive(Debug)]
pub struct ListOfPortConnectionsOrdered<'a> {
    pub nodes: (
        OrderedPortConnection<'a>,
        Vec<(Symbol<'a>, OrderedPortConnection<'a>)>,
    ),
}

#[derive(Debug)]
pub struct ListOfPortConnectionsNamed<'a> {
    pub nodes: (
        NamedPortConnection<'a>,
        Vec<(Symbol<'a>, NamedPortConnection<'a>)>,
    ),
}

#[derive(Debug)]
pub struct OrderedPortConnection<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, Option<Expression<'a>>),
}

#[derive(Debug)]
pub enum NamedPortConnection<'a> {
    Identifier(NamedPortConnectionIdentifier<'a>),
    Asterisk(NamedPortConnectionAsterisk<'a>),
}

#[derive(Debug)]
pub struct NamedPortConnectionIdentifier<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Symbol<'a>,
        PortIdentifier<'a>,
        Option<(Symbol<'a>, Option<Expression<'a>>, Symbol<'a>)>,
    ),
}

#[derive(Debug)]
pub struct NamedPortConnectionAsterisk<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, Symbol<'a>),
}

// -----------------------------------------------------------------------------

pub fn module_instantiation(s: Span) -> IResult<Span, ModuleInstantiation> {
    let (s, a) = module_identifier(s)?;
    let (s, b) = opt(parameter_value_assignment)(s)?;
    let (s, c) = hierarchical_instance(s)?;
    let (s, d) = many0(pair(symbol(","), hierarchical_instance))(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        ModuleInstantiation {
            nodes: (a, b, c, d, e),
        },
    ))
}

pub fn parameter_value_assignment(s: Span) -> IResult<Span, ParameterValueAssignment> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = paren2(opt(list_of_parameter_assignments))(s)?;
    Ok((s, ParameterValueAssignment { nodes: (a, b) }))
}

pub fn list_of_parameter_assignments(s: Span) -> IResult<Span, ListOfParameterAssignments> {
    alt((
        list_of_parameter_assignments_ordered,
        list_of_parameter_assignments_named,
    ))(s)
}

pub fn list_of_parameter_assignments_ordered(s: Span) -> IResult<Span, ListOfParameterAssignments> {
    let (s, a) = ordered_parameter_assignment(s)?;
    let (s, b) = many0(pair(symbol(","), ordered_parameter_assignment))(s)?;
    Ok((
        s,
        ListOfParameterAssignments::Ordered(ListOfParameterAssignmentsOrdered { nodes: (a, b) }),
    ))
}

pub fn list_of_parameter_assignments_named(s: Span) -> IResult<Span, ListOfParameterAssignments> {
    let (s, a) = named_parameter_assignment(s)?;
    let (s, b) = many0(pair(symbol(","), named_parameter_assignment))(s)?;
    Ok((
        s,
        ListOfParameterAssignments::Named(ListOfParameterAssignmentsNamed { nodes: (a, b) }),
    ))
}

pub fn ordered_parameter_assignment(s: Span) -> IResult<Span, OrderedParameterAssignment> {
    let (s, x) = param_expression(s)?;
    Ok((s, OrderedParameterAssignment { nodes: (x,) }))
}

pub fn named_parameter_assignment(s: Span) -> IResult<Span, NamedParameterAssignment> {
    let (s, a) = symbol(".")(s)?;
    let (s, b) = parameter_identifier(s)?;
    let (s, c) = paren2(opt(param_expression))(s)?;
    Ok((s, NamedParameterAssignment { nodes: (a, b, c) }))
}

pub fn hierarchical_instance(s: Span) -> IResult<Span, HierarchicalInstance> {
    let (s, a) = name_of_instance(s)?;
    let (s, b) = paren2(opt(list_of_port_connections))(s)?;
    Ok((s, HierarchicalInstance { nodes: (a, b) }))
}

pub fn name_of_instance(s: Span) -> IResult<Span, NameOfInstance> {
    let (s, x) = instance_identifier(s)?;
    let (s, y) = many0(unpacked_dimension)(s)?;
    Ok((s, NameOfInstance { nodes: (x, y) }))
}

pub fn list_of_port_connections(s: Span) -> IResult<Span, ListOfPortConnections> {
    alt((
        list_of_port_connections_ordered,
        list_of_port_connections_named,
    ))(s)
}

pub fn list_of_port_connections_ordered(s: Span) -> IResult<Span, ListOfPortConnections> {
    let (s, a) = ordered_port_connection(s)?;
    let (s, b) = many0(pair(symbol(","), ordered_port_connection))(s)?;
    Ok((
        s,
        ListOfPortConnections::Ordered(ListOfPortConnectionsOrdered { nodes: (a, b) }),
    ))
}

pub fn list_of_port_connections_named(s: Span) -> IResult<Span, ListOfPortConnections> {
    let (s, a) = named_port_connection(s)?;
    let (s, b) = many0(pair(symbol(","), named_port_connection))(s)?;
    Ok((
        s,
        ListOfPortConnections::Named(ListOfPortConnectionsNamed { nodes: (a, b) }),
    ))
}

pub fn ordered_port_connection(s: Span) -> IResult<Span, OrderedPortConnection> {
    let (s, x) = many0(attribute_instance)(s)?;
    let (s, y) = opt(expression)(s)?;
    Ok((s, OrderedPortConnection { nodes: (x, y) }))
}

pub fn named_port_connection(s: Span) -> IResult<Span, NamedPortConnection> {
    alt((
        named_port_connection_identifier,
        named_port_connection_asterisk,
    ))(s)
}

pub fn named_port_connection_identifier(s: Span) -> IResult<Span, NamedPortConnection> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = port_identifier(s)?;
    let (s, d) = opt(paren2(opt(expression)))(s)?;
    Ok((
        s,
        NamedPortConnection::Identifier(NamedPortConnectionIdentifier {
            nodes: (a, b, c, d),
        }),
    ))
}

pub fn named_port_connection_asterisk(s: Span) -> IResult<Span, NamedPortConnection> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol(".*")(s)?;
    Ok((
        s,
        NamedPortConnection::Asterisk(NamedPortConnectionAsterisk { nodes: (a, b) }),
    ))
}

// -----------------------------------------------------------------------------
