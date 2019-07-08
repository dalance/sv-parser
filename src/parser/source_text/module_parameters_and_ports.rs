use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum ParameterPortList<'a> {
    Assignment(ParameterPortListAssignment<'a>),
    Declaration(ParameterPortListDeclaration<'a>),
    Empty,
}

#[derive(Debug)]
pub struct ParameterPortListAssignment<'a> {
    pub nodes: (
        ListOfParamAssignments<'a>,
        Vec<ParameterPortDeclaration<'a>>,
    ),
}

#[derive(Debug)]
pub struct ParameterPortListDeclaration<'a> {
    pub nodes: (Vec<ParameterPortDeclaration<'a>>,),
}

#[derive(Debug)]
pub enum ParameterPortDeclaration<'a> {
    ParameterDeclaration(ParameterDeclaration<'a>),
    LocalParameterDeclaration(LocalParameterDeclaration<'a>),
    ParamList(ParameterPortDeclarationParamList<'a>),
    TypeList(ParameterPortDeclarationTypeList<'a>),
}

#[derive(Debug)]
pub struct ParameterPortDeclarationParamList<'a> {
    pub nodes: (DataType<'a>, ListOfParamAssignments<'a>),
}

#[derive(Debug)]
pub struct ParameterPortDeclarationTypeList<'a> {
    pub nodes: (ListOfTypeAssignments<'a>,),
}

#[derive(Debug)]
pub struct ListOfPorts<'a> {
    pub nodes: (Vec<Port<'a>>,),
}

#[derive(Debug)]
pub struct ListOfPortDeclarations<'a> {
    pub nodes: (Option<Vec<(Vec<AttributeInstance<'a>>, AnsiPortDeclaration<'a>)>>,),
}

#[derive(Debug)]
pub enum PortDeclaration<'a> {
    Inout(PortDeclarationInout<'a>),
    Input(PortDeclarationInput<'a>),
    Output(PortDeclarationOutput<'a>),
    Ref(PortDeclarationRef<'a>),
    Interface(PortDeclarationInterface<'a>),
}

#[derive(Debug)]
pub struct PortDeclarationInout<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, InoutDeclaration<'a>),
}

#[derive(Debug)]
pub struct PortDeclarationInput<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, InputDeclaration<'a>),
}

#[derive(Debug)]
pub struct PortDeclarationOutput<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, OutputDeclaration<'a>),
}

#[derive(Debug)]
pub struct PortDeclarationRef<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, RefDeclaration<'a>),
}

#[derive(Debug)]
pub struct PortDeclarationInterface<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, InterfacePortDeclaration<'a>),
}

#[derive(Debug)]
pub enum Port<'a> {
    NonNamed(PortNonNamed<'a>),
    Named(PortNamed<'a>),
}

#[derive(Debug)]
pub struct PortNonNamed<'a> {
    pub nodes: (Option<PortExpression<'a>>,),
}

#[derive(Debug)]
pub struct PortNamed<'a> {
    pub nodes: (PortIdentifier<'a>, Option<PortExpression<'a>>),
}

#[derive(Debug)]
pub enum PortExpression<'a> {
    PortReference(PortReference<'a>),
    Bracket(PortExpressionBracket<'a>),
}

#[derive(Debug)]
pub struct PortExpressionBracket<'a> {
    pub nodes: (Vec<PortReference<'a>>,),
}

#[derive(Debug)]
pub struct PortReference<'a> {
    pub nodes: (PortIdentifier<'a>, ConstantSelect<'a>),
}

#[derive(Debug)]
pub enum PortDirection {
    Input,
    Output,
    Inout,
    Ref,
}

#[derive(Debug)]
pub struct NetPortHeader<'a> {
    pub nodes: (Option<PortDirection>, NetPortType<'a>),
}

#[derive(Debug)]
pub struct VariablePortHeader<'a> {
    pub nodes: (Option<PortDirection>, VariablePortType<'a>),
}

#[derive(Debug)]
pub enum InterfacePortHeader<'a> {
    Identifier(InterfacePortHeaderIdentifier<'a>),
    Interface(InterfacePortHeaderInterface<'a>),
}

#[derive(Debug)]
pub struct InterfacePortHeaderIdentifier<'a> {
    pub nodes: (InterfaceIdentifier<'a>, Option<ModportIdentifier<'a>>),
}

#[derive(Debug)]
pub struct InterfacePortHeaderInterface<'a> {
    pub nodes: (Option<ModportIdentifier<'a>>,),
}

#[derive(Debug)]
pub enum NetPortHeaderOrInterfacePortHeader<'a> {
    NetPortHeader(NetPortHeader<'a>),
    InterfacePortHeader(InterfacePortHeader<'a>),
}
#[derive(Debug)]
pub enum AnsiPortDeclaration<'a> {
    Net(AnsiPortDeclarationNet<'a>),
    Variable(AnsiPortDeclarationVariable<'a>),
    Paren(AnsiPortDeclarationParen<'a>),
}

#[derive(Debug)]
pub struct AnsiPortDeclarationNet<'a> {
    pub nodes: (
        Option<NetPortHeaderOrInterfacePortHeader<'a>>,
        PortIdentifier<'a>,
        Vec<UnpackedDimension<'a>>,
        Option<ConstantExpression<'a>>,
    ),
}

#[derive(Debug)]
pub struct AnsiPortDeclarationVariable<'a> {
    pub nodes: (
        Option<VariablePortHeader<'a>>,
        PortIdentifier<'a>,
        Vec<VariableDimension<'a>>,
        Option<ConstantExpression<'a>>,
    ),
}

#[derive(Debug)]
pub struct AnsiPortDeclarationParen<'a> {
    pub nodes: (
        Option<PortDirection>,
        PortIdentifier<'a>,
        Option<Expression<'a>>,
    ),
}

// -----------------------------------------------------------------------------

pub fn parameter_port_list(s: &str) -> IResult<&str, ParameterPortList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn parameter_port_declaration(s: &str) -> IResult<&str, ParameterPortDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn list_of_ports(s: &str) -> IResult<&str, ListOfPorts> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn list_of_port_declarations(s: &str) -> IResult<&str, ListOfPortDeclarations> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn port_declaration(s: &str) -> IResult<&str, PortDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn port(s: &str) -> IResult<&str, Port> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn port_expression(s: &str) -> IResult<&str, PortExpression> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn port_reference(s: &str) -> IResult<&str, PortReference> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn port_direction(s: &str) -> IResult<&str, PortDirection> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn net_port_header(s: &str) -> IResult<&str, NetPortHeader> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn variable_port_header(s: &str) -> IResult<&str, VariablePortHeader> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn interface_port_header(s: &str) -> IResult<&str, InterfacePortHeader> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn ansi_port_declaration(s: &str) -> IResult<&str, AnsiPortDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}
