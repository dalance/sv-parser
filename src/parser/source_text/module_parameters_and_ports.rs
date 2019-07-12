use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum ParameterPortList<'a> {
    Assignment(ParameterPortListAssignment<'a>),
    Declaration(ParameterPortListDeclaration<'a>),
    Empty(Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct ParameterPortListAssignment<'a> {
    pub nodes: (
        ListOfParamAssignments<'a>,
        Vec<ParameterPortDeclaration<'a>>,
    ),
}

#[derive(Debug, Node)]
pub struct ParameterPortListDeclaration<'a> {
    pub nodes: (Vec<ParameterPortDeclaration<'a>>,),
}

#[derive(Debug, Node)]
pub enum ParameterPortDeclaration<'a> {
    ParameterDeclaration(ParameterDeclaration<'a>),
    LocalParameterDeclaration(LocalParameterDeclaration<'a>),
    ParamList(ParameterPortDeclarationParamList<'a>),
    TypeList(ParameterPortDeclarationTypeList<'a>),
}

#[derive(Debug, Node)]
pub struct ParameterPortDeclarationParamList<'a> {
    pub nodes: (DataType<'a>, ListOfParamAssignments<'a>),
}

#[derive(Debug, Node)]
pub struct ParameterPortDeclarationTypeList<'a> {
    pub nodes: (ListOfTypeAssignments<'a>,),
}

#[derive(Debug, Node)]
pub struct ListOfPorts<'a> {
    pub nodes: (Vec<Port<'a>>,),
}

#[derive(Debug, Node)]
pub struct ListOfPortDeclarations<'a> {
    pub nodes: (Option<Vec<(Vec<AttributeInstance<'a>>, AnsiPortDeclaration<'a>)>>,),
}

#[derive(Debug, Node)]
pub enum PortDeclaration<'a> {
    Inout(PortDeclarationInout<'a>),
    Input(PortDeclarationInput<'a>),
    Output(PortDeclarationOutput<'a>),
    Ref(PortDeclarationRef<'a>),
    Interface(PortDeclarationInterface<'a>),
}

#[derive(Debug, Node)]
pub struct PortDeclarationInout<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, InoutDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct PortDeclarationInput<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, InputDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct PortDeclarationOutput<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, OutputDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct PortDeclarationRef<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, RefDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct PortDeclarationInterface<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, InterfacePortDeclaration<'a>),
}

#[derive(Debug, Node)]
pub enum Port<'a> {
    NonNamed(PortNonNamed<'a>),
    Named(PortNamed<'a>),
}

#[derive(Debug, Node)]
pub struct PortNonNamed<'a> {
    pub nodes: (Option<PortExpression<'a>>,),
}

#[derive(Debug, Node)]
pub struct PortNamed<'a> {
    pub nodes: (PortIdentifier<'a>, Option<PortExpression<'a>>),
}

#[derive(Debug, Node)]
pub enum PortExpression<'a> {
    PortReference(PortReference<'a>),
    Bracket(PortExpressionBracket<'a>),
}

#[derive(Debug, Node)]
pub struct PortExpressionBracket<'a> {
    pub nodes: (Vec<PortReference<'a>>,),
}

#[derive(Debug, Node)]
pub struct PortReference<'a> {
    pub nodes: (PortIdentifier<'a>, ConstantSelect<'a>),
}

#[derive(Debug, Node)]
pub enum PortDirection<'a> {
    Input(Symbol<'a>),
    Output(Symbol<'a>),
    Inout(Symbol<'a>),
    Ref(Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct NetPortHeader<'a> {
    pub nodes: (Option<PortDirection<'a>>, NetPortType<'a>),
}

#[derive(Debug, Node)]
pub struct VariablePortHeader<'a> {
    pub nodes: (Option<PortDirection<'a>>, VariablePortType<'a>),
}

#[derive(Debug, Node)]
pub enum InterfacePortHeader<'a> {
    Identifier(InterfacePortHeaderIdentifier<'a>),
    Interface(InterfacePortHeaderInterface<'a>),
}

#[derive(Debug, Node)]
pub struct InterfacePortHeaderIdentifier<'a> {
    pub nodes: (InterfaceIdentifier<'a>, Option<ModportIdentifier<'a>>),
}

#[derive(Debug, Node)]
pub struct InterfacePortHeaderInterface<'a> {
    pub nodes: (Option<ModportIdentifier<'a>>,),
}

#[derive(Debug, Node)]
pub enum NetPortHeaderOrInterfacePortHeader<'a> {
    NetPortHeader(NetPortHeader<'a>),
    InterfacePortHeader(InterfacePortHeader<'a>),
}
#[derive(Debug, Node)]
pub enum AnsiPortDeclaration<'a> {
    Net(AnsiPortDeclarationNet<'a>),
    Variable(AnsiPortDeclarationVariable<'a>),
    Paren(AnsiPortDeclarationParen<'a>),
}

#[derive(Debug, Node)]
pub struct AnsiPortDeclarationNet<'a> {
    pub nodes: (
        Option<NetPortHeaderOrInterfacePortHeader<'a>>,
        PortIdentifier<'a>,
        Vec<UnpackedDimension<'a>>,
        Option<ConstantExpression<'a>>,
    ),
}

#[derive(Debug, Node)]
pub struct AnsiPortDeclarationVariable<'a> {
    pub nodes: (
        Option<VariablePortHeader<'a>>,
        PortIdentifier<'a>,
        Vec<VariableDimension<'a>>,
        Option<ConstantExpression<'a>>,
    ),
}

#[derive(Debug, Node)]
pub struct AnsiPortDeclarationParen<'a> {
    pub nodes: (
        Option<PortDirection<'a>>,
        PortIdentifier<'a>,
        Option<Expression<'a>>,
    ),
}

// -----------------------------------------------------------------------------

pub fn parameter_port_list(s: Span) -> IResult<Span, ParameterPortList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn parameter_port_declaration(s: Span) -> IResult<Span, ParameterPortDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn list_of_ports(s: Span) -> IResult<Span, ListOfPorts> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn list_of_port_declarations(s: Span) -> IResult<Span, ListOfPortDeclarations> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn port_declaration(s: Span) -> IResult<Span, PortDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn port(s: Span) -> IResult<Span, Port> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn port_expression(s: Span) -> IResult<Span, PortExpression> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn port_reference(s: Span) -> IResult<Span, PortReference> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn port_direction(s: Span) -> IResult<Span, PortDirection> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn net_port_header(s: Span) -> IResult<Span, NetPortHeader> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn variable_port_header(s: Span) -> IResult<Span, VariablePortHeader> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn interface_port_header(s: Span) -> IResult<Span, InterfacePortHeader> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn ansi_port_declaration(s: Span) -> IResult<Span, AnsiPortDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}
