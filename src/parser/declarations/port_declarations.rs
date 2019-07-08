use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct InoutDeclaration<'a> {
    pub nodes: (NetPortType<'a>, ListOfPortIdentifiers<'a>),
}

#[derive(Debug)]
pub enum InputDeclaration<'a> {
    Net(InputDeclarationNet<'a>),
    Variable(InputDeclarationVariable<'a>),
}

#[derive(Debug)]
pub struct InputDeclarationNet<'a> {
    pub nodes: (NetPortType<'a>, ListOfPortIdentifiers<'a>),
}

#[derive(Debug)]
pub struct InputDeclarationVariable<'a> {
    pub nodes: (VariablePortType<'a>, ListOfVariableIdentifiers<'a>),
}

#[derive(Debug)]
pub enum OutputDeclaration<'a> {
    Net(OutputDeclarationNet<'a>),
    Variable(OutputDeclarationVariable<'a>),
}

#[derive(Debug)]
pub struct OutputDeclarationNet<'a> {
    pub nodes: (NetPortType<'a>, ListOfPortIdentifiers<'a>),
}

#[derive(Debug)]
pub struct OutputDeclarationVariable<'a> {
    pub nodes: (VariablePortType<'a>, ListOfVariableIdentifiers<'a>),
}

#[derive(Debug)]
pub struct InterfacePortDeclaration<'a> {
    pub nodes: (
        InterfaceIdentifier<'a>,
        Option<ModportIdentifier<'a>>,
        ListOfInterfaceIdentifiers<'a>,
    ),
}

#[derive(Debug)]
pub struct RefDeclaration<'a> {
    pub nodes: (VariablePortType<'a>, ListOfVariableIdentifiers<'a>),
}

// -----------------------------------------------------------------------------

pub fn inout_declaratrion(s: &str) -> IResult<&str, InoutDeclaration> {
    let (s, _) = symbol("inout")(s)?;
    let (s, x) = net_port_type(s)?;
    let (s, y) = list_of_port_identifiers(s)?;
    Ok((s, InoutDeclaration { nodes: (x, y) }))
}

pub fn input_declaratrion(s: &str) -> IResult<&str, InputDeclaration> {
    alt((input_declaration_net, input_declaration_variable))(s)
}

pub fn input_declaration_net(s: &str) -> IResult<&str, InputDeclaration> {
    let (s, _) = symbol("input")(s)?;
    let (s, x) = net_port_type(s)?;
    let (s, y) = list_of_port_identifiers(s)?;
    Ok((
        s,
        InputDeclaration::Net(InputDeclarationNet { nodes: (x, y) }),
    ))
}

pub fn input_declaration_variable(s: &str) -> IResult<&str, InputDeclaration> {
    let (s, _) = symbol("input")(s)?;
    let (s, x) = variable_port_type(s)?;
    let (s, y) = list_of_variable_identifiers(s)?;
    Ok((
        s,
        InputDeclaration::Variable(InputDeclarationVariable { nodes: (x, y) }),
    ))
}

pub fn output_declaratrion(s: &str) -> IResult<&str, OutputDeclaration> {
    alt((output_declaration_net, output_declaration_variable))(s)
}

pub fn output_declaration_net(s: &str) -> IResult<&str, OutputDeclaration> {
    let (s, _) = symbol("output")(s)?;
    let (s, x) = net_port_type(s)?;
    let (s, y) = list_of_port_identifiers(s)?;
    Ok((
        s,
        OutputDeclaration::Net(OutputDeclarationNet { nodes: (x, y) }),
    ))
}

pub fn output_declaration_variable(s: &str) -> IResult<&str, OutputDeclaration> {
    let (s, _) = symbol("output")(s)?;
    let (s, x) = variable_port_type(s)?;
    let (s, y) = list_of_variable_identifiers(s)?;
    Ok((
        s,
        OutputDeclaration::Variable(OutputDeclarationVariable { nodes: (x, y) }),
    ))
}

pub fn interface_port_declaration(s: &str) -> IResult<&str, InterfacePortDeclaration> {
    let (s, x) = interface_identifier(s)?;
    let (s, y) = opt(preceded(symbol("."), modport_identifier))(s)?;
    let (s, z) = list_of_interface_identifiers(s)?;
    Ok((s, InterfacePortDeclaration { nodes: (x, y, z) }))
}

pub fn ref_declaration(s: &str) -> IResult<&str, RefDeclaration> {
    let (s, _) = symbol("ref")(s)?;
    let (s, x) = variable_port_type(s)?;
    let (s, y) = list_of_variable_identifiers(s)?;
    Ok((s, RefDeclaration { nodes: (x, y) }))
}
