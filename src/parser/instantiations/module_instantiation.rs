use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct ModuleInstantiation<'a> {
    pub nodes: (
        ModuleIdentifier<'a>,
        Option<ParameterValueAssignment<'a>>,
        List<Symbol<'a>, HierarchicalInstance<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ParameterValueAssignment<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<'a, Option<ListOfParameterAssignments<'a>>>,
    ),
}

#[derive(Debug, Node)]
pub enum ListOfParameterAssignments<'a> {
    Ordered(ListOfParameterAssignmentsOrdered<'a>),
    Named(ListOfParameterAssignmentsNamed<'a>),
}

#[derive(Debug, Node)]
pub struct ListOfParameterAssignmentsOrdered<'a> {
    pub nodes: (List<Symbol<'a>, OrderedParameterAssignment<'a>>,),
}

#[derive(Debug, Node)]
pub struct ListOfParameterAssignmentsNamed<'a> {
    pub nodes: (List<Symbol<'a>, NamedParameterAssignment<'a>>,),
}

#[derive(Debug, Node)]
pub struct OrderedParameterAssignment<'a> {
    pub nodes: (ParamExpression<'a>,),
}

#[derive(Debug, Node)]
pub struct NamedParameterAssignment<'a> {
    pub nodes: (
        Symbol<'a>,
        ParameterIdentifier<'a>,
        Paren<'a, Option<ParamExpression<'a>>>,
    ),
}

#[derive(Debug, Node)]
pub struct HierarchicalInstance<'a> {
    pub nodes: (
        NameOfInstance<'a>,
        Paren<'a, Option<ListOfPortConnections<'a>>>,
    ),
}

#[derive(Debug, Node)]
pub struct NameOfInstance<'a> {
    pub nodes: (InstanceIdentifier<'a>, Vec<UnpackedDimension<'a>>),
}

#[derive(Debug, Node)]
pub enum ListOfPortConnections<'a> {
    Ordered(ListOfPortConnectionsOrdered<'a>),
    Named(ListOfPortConnectionsNamed<'a>),
}

#[derive(Debug, Node)]
pub struct ListOfPortConnectionsOrdered<'a> {
    pub nodes: (List<Symbol<'a>, OrderedPortConnection<'a>>,),
}

#[derive(Debug, Node)]
pub struct ListOfPortConnectionsNamed<'a> {
    pub nodes: (List<Symbol<'a>, NamedPortConnection<'a>>,),
}

#[derive(Debug, Node)]
pub struct OrderedPortConnection<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, Option<Expression<'a>>),
}

#[derive(Debug, Node)]
pub enum NamedPortConnection<'a> {
    Identifier(NamedPortConnectionIdentifier<'a>),
    Asterisk(NamedPortConnectionAsterisk<'a>),
}

#[derive(Debug, Node)]
pub struct NamedPortConnectionIdentifier<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Symbol<'a>,
        PortIdentifier<'a>,
        Option<Paren<'a, Option<Expression<'a>>>>,
    ),
}

#[derive(Debug, Node)]
pub struct NamedPortConnectionAsterisk<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, Symbol<'a>),
}

// -----------------------------------------------------------------------------

#[trace]
pub fn module_instantiation(s: Span) -> IResult<Span, ModuleInstantiation> {
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

#[trace]
pub fn parameter_value_assignment(s: Span) -> IResult<Span, ParameterValueAssignment> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = paren(opt(list_of_parameter_assignments))(s)?;
    Ok((s, ParameterValueAssignment { nodes: (a, b) }))
}

#[trace]
pub fn list_of_parameter_assignments(s: Span) -> IResult<Span, ListOfParameterAssignments> {
    alt((
        list_of_parameter_assignments_ordered,
        list_of_parameter_assignments_named,
    ))(s)
}

#[trace]
pub fn list_of_parameter_assignments_ordered(s: Span) -> IResult<Span, ListOfParameterAssignments> {
    let (s, a) = list(symbol(","), ordered_parameter_assignment)(s)?;
    Ok((
        s,
        ListOfParameterAssignments::Ordered(ListOfParameterAssignmentsOrdered { nodes: (a,) }),
    ))
}

#[trace]
pub fn list_of_parameter_assignments_named(s: Span) -> IResult<Span, ListOfParameterAssignments> {
    let (s, a) = list(symbol(","), named_parameter_assignment)(s)?;
    Ok((
        s,
        ListOfParameterAssignments::Named(ListOfParameterAssignmentsNamed { nodes: (a,) }),
    ))
}

#[trace]
pub fn ordered_parameter_assignment(s: Span) -> IResult<Span, OrderedParameterAssignment> {
    let (s, x) = param_expression(s)?;
    Ok((s, OrderedParameterAssignment { nodes: (x,) }))
}

#[trace]
pub fn named_parameter_assignment(s: Span) -> IResult<Span, NamedParameterAssignment> {
    let (s, a) = symbol(".")(s)?;
    let (s, b) = parameter_identifier(s)?;
    let (s, c) = paren(opt(param_expression))(s)?;
    Ok((s, NamedParameterAssignment { nodes: (a, b, c) }))
}

#[trace]
pub fn hierarchical_instance(s: Span) -> IResult<Span, HierarchicalInstance> {
    let (s, a) = name_of_instance(s)?;
    let (s, b) = paren(opt(list_of_port_connections))(s)?;
    Ok((s, HierarchicalInstance { nodes: (a, b) }))
}

#[trace]
pub fn name_of_instance(s: Span) -> IResult<Span, NameOfInstance> {
    let (s, x) = instance_identifier(s)?;
    let (s, y) = many0(unpacked_dimension)(s)?;
    Ok((s, NameOfInstance { nodes: (x, y) }))
}

#[trace]
pub fn list_of_port_connections(s: Span) -> IResult<Span, ListOfPortConnections> {
    alt((
        list_of_port_connections_ordered,
        list_of_port_connections_named,
    ))(s)
}

#[trace]
pub fn list_of_port_connections_ordered(s: Span) -> IResult<Span, ListOfPortConnections> {
    let (s, a) = list(symbol(","), ordered_port_connection)(s)?;
    Ok((
        s,
        ListOfPortConnections::Ordered(ListOfPortConnectionsOrdered { nodes: (a,) }),
    ))
}

#[trace]
pub fn list_of_port_connections_named(s: Span) -> IResult<Span, ListOfPortConnections> {
    let (s, a) = list(symbol(","), named_port_connection)(s)?;
    Ok((
        s,
        ListOfPortConnections::Named(ListOfPortConnectionsNamed { nodes: (a,) }),
    ))
}

#[trace]
pub fn ordered_port_connection(s: Span) -> IResult<Span, OrderedPortConnection> {
    let (s, x) = many0(attribute_instance)(s)?;
    let (s, y) = opt(expression)(s)?;
    Ok((s, OrderedPortConnection { nodes: (x, y) }))
}

#[trace]
pub fn named_port_connection(s: Span) -> IResult<Span, NamedPortConnection> {
    alt((
        named_port_connection_identifier,
        named_port_connection_asterisk,
    ))(s)
}

#[trace]
pub fn named_port_connection_identifier(s: Span) -> IResult<Span, NamedPortConnection> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = port_identifier(s)?;
    let (s, d) = opt(paren(opt(expression)))(s)?;
    Ok((
        s,
        NamedPortConnection::Identifier(NamedPortConnectionIdentifier {
            nodes: (a, b, c, d),
        }),
    ))
}

#[trace]
pub fn named_port_connection_asterisk(s: Span) -> IResult<Span, NamedPortConnection> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol(".*")(s)?;
    Ok((
        s,
        NamedPortConnection::Asterisk(NamedPortConnectionAsterisk { nodes: (a, b) }),
    ))
}

// -----------------------------------------------------------------------------
