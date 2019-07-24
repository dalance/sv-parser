use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct UdpPortList {
    pub nodes: (
        OutputPortIdentifier,
        Symbol,
        List<Symbol, InputPortIdentifier>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct UdpDeclarationPortList {
    pub nodes: (
        UdpOutputDeclaration,
        Symbol,
        List<Symbol, UdpInputDeclaration>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum UdpPortDeclaration {
    UdpOutputDeclaration((UdpOutputDeclaration, Symbol)),
    UdpInputDeclaration((UdpInputDeclaration, Symbol)),
    UdpRegDeclaration((UdpRegDeclaration, Symbol)),
}

#[derive(Clone, Debug, Node)]
pub enum UdpOutputDeclaration {
    Nonreg(UdpOutputDeclarationNonreg),
    Reg(UdpOutputDeclarationReg),
}

#[derive(Clone, Debug, Node)]
pub struct UdpOutputDeclarationNonreg {
    pub nodes: (Vec<AttributeInstance>, Keyword, PortIdentifier),
}

#[derive(Clone, Debug, Node)]
pub struct UdpOutputDeclarationReg {
    pub nodes: (
        Vec<AttributeInstance>,
        Keyword,
        Keyword,
        PortIdentifier,
        Option<(Symbol, ConstantExpression)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct UdpInputDeclaration {
    pub nodes: (Vec<AttributeInstance>, Keyword, ListOfUdpPortIdentifiers),
}

#[derive(Clone, Debug, Node)]
pub struct UdpRegDeclaration {
    pub nodes: (Vec<AttributeInstance>, Keyword, VariableIdentifier),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn udp_port_list(s: Span) -> IResult<Span, UdpPortList> {
    let (s, a) = output_port_identifier(s)?;
    let (s, b) = symbol(",")(s)?;
    let (s, c) = list(symbol(","), input_port_identifier)(s)?;
    Ok((s, UdpPortList { nodes: (a, b, c) }))
}

#[parser]
pub fn udp_declaration_port_list(s: Span) -> IResult<Span, UdpDeclarationPortList> {
    let (s, a) = udp_output_declaration(s)?;
    let (s, b) = symbol(",")(s)?;
    let (s, c) = list(symbol(","), udp_input_declaration)(s)?;
    Ok((s, UdpDeclarationPortList { nodes: (a, b, c) }))
}

#[parser]
pub fn udp_port_declaration(s: Span) -> IResult<Span, UdpPortDeclaration> {
    alt((
        map(pair(udp_output_declaration, symbol(";")), |x| {
            UdpPortDeclaration::UdpOutputDeclaration(x)
        }),
        map(pair(udp_input_declaration, symbol(";")), |x| {
            UdpPortDeclaration::UdpInputDeclaration(x)
        }),
        map(pair(udp_reg_declaration, symbol(";")), |x| {
            UdpPortDeclaration::UdpRegDeclaration(x)
        }),
    ))(s)
}

#[parser]
pub fn udp_output_declaration(s: Span) -> IResult<Span, UdpOutputDeclaration> {
    alt((udp_output_declaration_nonreg, udp_output_declaration_reg))(s)
}

#[parser]
pub fn udp_output_declaration_nonreg(s: Span) -> IResult<Span, UdpOutputDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = keyword("output")(s)?;
    let (s, c) = port_identifier(s)?;
    Ok((
        s,
        UdpOutputDeclaration::Nonreg(UdpOutputDeclarationNonreg { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn udp_output_declaration_reg(s: Span) -> IResult<Span, UdpOutputDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = keyword("output")(s)?;
    let (s, c) = keyword("reg")(s)?;
    let (s, d) = port_identifier(s)?;
    let (s, e) = opt(pair(symbol("="), constant_expression))(s)?;
    Ok((
        s,
        UdpOutputDeclaration::Reg(UdpOutputDeclarationReg {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn udp_input_declaration(s: Span) -> IResult<Span, UdpInputDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = keyword("input")(s)?;
    let (s, c) = list_of_udp_port_identifiers(s)?;
    Ok((s, UdpInputDeclaration { nodes: (a, b, c) }))
}

#[parser]
pub fn udp_reg_declaration(s: Span) -> IResult<Span, UdpRegDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = keyword("reg")(s)?;
    let (s, c) = variable_identifier(s)?;
    Ok((s, UdpRegDeclaration { nodes: (a, b, c) }))
}
