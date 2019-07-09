use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct ModuleInstantiation<'a> {
    pub nodes: (
        ModuleIdentifier<'a>,
        Option<ParameterValueAssignment<'a>>,
        Vec<HierarchicalInstance<'a>>,
    ),
}

#[derive(Debug)]
pub struct ParameterValueAssignment<'a> {
    pub nodes: (ListOfParameterAssignments<'a>,),
}

#[derive(Debug)]
pub enum ListOfParameterAssignments<'a> {
    Ordered(Vec<OrderedParameterAssignment<'a>>),
    Named(Vec<NamedParameterAssignment<'a>>),
}

#[derive(Debug)]
pub struct OrderedParameterAssignment<'a> {
    pub nodes: (ParamExpression<'a>,),
}

#[derive(Debug)]
pub struct NamedParameterAssignment<'a> {
    pub nodes: (ParameterIdentifier<'a>, Option<ParamExpression<'a>>),
}

#[derive(Debug)]
pub struct HierarchicalInstance<'a> {
    pub nodes: (NameOfInstance<'a>, Option<ListOfPortConnections<'a>>),
}

#[derive(Debug)]
pub struct NameOfInstance<'a> {
    pub nodes: (InstanceIdentifier<'a>, Vec<UnpackedDimension<'a>>),
}

#[derive(Debug)]
pub enum ListOfPortConnections<'a> {
    Ordered(Vec<OrderedPortConnection<'a>>),
    Named(Vec<NamedPortConnection<'a>>),
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
        PortIdentifier<'a>,
        Option<Expression<'a>>,
    ),
}

#[derive(Debug)]
pub struct NamedPortConnectionAsterisk<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>,),
}

// -----------------------------------------------------------------------------

pub fn module_instantiation(s: Span) -> IResult<Span, ModuleInstantiation> {
    let (s, x) = module_identifier(s)?;
    let (s, y) = opt(parameter_value_assignment)(s)?;
    let (s, z) = separated_nonempty_list(symbol(","), hierarchical_instance)(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, ModuleInstantiation { nodes: (x, y, z) }))
}

pub fn parameter_value_assignment(s: Span) -> IResult<Span, ParameterValueAssignment> {
    let (s, _) = symbol("#")(s)?;
    let (s, x) = paren(list_of_parameter_assignments)(s)?;
    Ok((s, ParameterValueAssignment { nodes: (x,) }))
}

pub fn list_of_parameter_assignments(s: Span) -> IResult<Span, ListOfParameterAssignments> {
    alt((
        map(
            separated_nonempty_list(symbol(","), ordered_parameter_assignment),
            |x| ListOfParameterAssignments::Ordered(x),
        ),
        map(
            separated_nonempty_list(symbol(","), named_parameter_assignment),
            |x| ListOfParameterAssignments::Named(x),
        ),
    ))(s)
}

pub fn ordered_parameter_assignment(s: Span) -> IResult<Span, OrderedParameterAssignment> {
    let (s, x) = param_expression(s)?;
    Ok((s, OrderedParameterAssignment { nodes: (x,) }))
}

pub fn named_parameter_assignment(s: Span) -> IResult<Span, NamedParameterAssignment> {
    let (s, _) = symbol(".")(s)?;
    let (s, x) = parameter_identifier(s)?;
    let (s, y) = paren(opt(param_expression))(s)?;
    Ok((s, NamedParameterAssignment { nodes: (x, y) }))
}

pub fn hierarchical_instance(s: Span) -> IResult<Span, HierarchicalInstance> {
    let (s, x) = name_of_instance(s)?;
    let (s, y) = paren(opt(list_of_port_connections))(s)?;
    Ok((s, HierarchicalInstance { nodes: (x, y) }))
}

pub fn name_of_instance(s: Span) -> IResult<Span, NameOfInstance> {
    let (s, x) = instance_identifier(s)?;
    let (s, y) = many0(unpacked_dimension)(s)?;
    Ok((s, NameOfInstance { nodes: (x, y) }))
}

pub fn list_of_port_connections(s: Span) -> IResult<Span, ListOfPortConnections> {
    alt((
        map(
            separated_nonempty_list(symbol(","), ordered_port_connection),
            |x| ListOfPortConnections::Ordered(x),
        ),
        map(
            separated_nonempty_list(symbol(","), named_port_connection),
            |x| ListOfPortConnections::Named(x),
        ),
    ))(s)
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
    let (s, x) = many0(attribute_instance)(s)?;
    let (s, _) = symbol(".")(s)?;
    let (s, y) = port_identifier(s)?;
    let (s, z) = opt(paren(opt(expression)))(s)?;
    let z = if let Some(Some(z)) = z { Some(z) } else { None };
    Ok((
        s,
        NamedPortConnection::Identifier(NamedPortConnectionIdentifier { nodes: (x, y, z) }),
    ))
}

pub fn named_port_connection_asterisk(s: Span) -> IResult<Span, NamedPortConnection> {
    let (s, x) = many0(attribute_instance)(s)?;
    let (s, _) = symbol(".")(s)?;
    let (s, _) = symbol("*")(s)?;
    Ok((
        s,
        NamedPortConnection::Asterisk(NamedPortConnectionAsterisk { nodes: (x,) }),
    ))
}

// -----------------------------------------------------------------------------
