use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct UdpNonansiDeclaration<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Symbol<'a>,
        UdpIdentifier<'a>,
        Paren<'a, UdpPortList<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct UdpAnsiDeclaration<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Symbol<'a>,
        UdpIdentifier<'a>,
        Paren<'a, UdpDeclarationPortList<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum UdpDeclaration<'a> {
    Nonansi(UdpDeclarationNonansi<'a>),
    Ansi(UdpDeclarationAnsi<'a>),
    ExternNonansi(UdpDeclarationExternNonansi<'a>),
    ExternAnsi(UdpDeclarationExternAnsi<'a>),
    Wildcard(UdpDeclarationWildcard<'a>),
}

#[derive(Debug, Node)]
pub struct UdpDeclarationNonansi<'a> {
    pub nodes: (
        UdpNonansiDeclaration<'a>,
        UdpPortDeclaration<'a>,
        Vec<UdpPortDeclaration<'a>>,
        UdpBody<'a>,
        Symbol<'a>,
        Option<(Symbol<'a>, UdpIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct UdpDeclarationAnsi<'a> {
    pub nodes: (
        UdpAnsiDeclaration<'a>,
        UdpBody<'a>,
        Symbol<'a>,
        Option<(Symbol<'a>, UdpIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct UdpDeclarationExternNonansi<'a> {
    pub nodes: (Symbol<'a>, UdpNonansiDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct UdpDeclarationExternAnsi<'a> {
    pub nodes: (Symbol<'a>, UdpAnsiDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct UdpDeclarationWildcard<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Symbol<'a>,
        UdpIdentifier<'a>,
        Paren<'a, Symbol<'a>>,
        Symbol<'a>,
        Vec<UdpPortDeclaration<'a>>,
        UdpBody<'a>,
        Symbol<'a>,
        Option<(Symbol<'a>, UdpIdentifier<'a>)>,
    ),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn udp_nonansi_declaration(s: Span) -> IResult<Span, UdpNonansiDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol("primitive")(s)?;
    let (s, c) = udp_identifier(s)?;
    let (s, d) = paren(udp_port_list)(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        UdpNonansiDeclaration {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser]
pub fn udp_ansi_declaration(s: Span) -> IResult<Span, UdpAnsiDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol("primitive")(s)?;
    let (s, c) = udp_identifier(s)?;
    let (s, d) = paren(udp_declaration_port_list)(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        UdpAnsiDeclaration {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser]
pub fn udp_declaration(s: Span) -> IResult<Span, UdpDeclaration> {
    alt((
        udp_declaration_nonansi,
        udp_declaration_ansi,
        udp_declaration_extern_nonansi,
        udp_declaration_extern_ansi,
        udp_declaration_wildcard,
    ))(s)
}

#[parser]
pub fn udp_declaration_nonansi(s: Span) -> IResult<Span, UdpDeclaration> {
    let (s, a) = udp_nonansi_declaration(s)?;
    let (s, b) = udp_port_declaration(s)?;
    let (s, c) = many0(udp_port_declaration)(s)?;
    let (s, d) = udp_body(s)?;
    let (s, e) = symbol("endprimitive")(s)?;
    let (s, f) = opt(pair(symbol(":"), udp_identifier))(s)?;
    Ok((
        s,
        UdpDeclaration::Nonansi(UdpDeclarationNonansi {
            nodes: (a, b, c, d, e, f),
        }),
    ))
}

#[parser]
pub fn udp_declaration_ansi(s: Span) -> IResult<Span, UdpDeclaration> {
    let (s, a) = udp_ansi_declaration(s)?;
    let (s, b) = udp_body(s)?;
    let (s, c) = symbol("endprimitive")(s)?;
    let (s, d) = opt(pair(symbol(":"), udp_identifier))(s)?;
    Ok((
        s,
        UdpDeclaration::Ansi(UdpDeclarationAnsi {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn udp_declaration_extern_nonansi(s: Span) -> IResult<Span, UdpDeclaration> {
    let (s, a) = symbol("extern")(s)?;
    let (s, b) = udp_nonansi_declaration(s)?;
    Ok((
        s,
        UdpDeclaration::ExternNonansi(UdpDeclarationExternNonansi { nodes: (a, b) }),
    ))
}

#[parser]
pub fn udp_declaration_extern_ansi(s: Span) -> IResult<Span, UdpDeclaration> {
    let (s, a) = symbol("extern")(s)?;
    let (s, b) = udp_ansi_declaration(s)?;
    Ok((
        s,
        UdpDeclaration::ExternAnsi(UdpDeclarationExternAnsi { nodes: (a, b) }),
    ))
}

#[parser]
pub fn udp_declaration_wildcard(s: Span) -> IResult<Span, UdpDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol("primitive")(s)?;
    let (s, c) = udp_identifier(s)?;
    let (s, d) = paren(symbol(".*"))(s)?;
    let (s, e) = symbol(";")(s)?;
    let (s, f) = many0(udp_port_declaration)(s)?;
    let (s, g) = udp_body(s)?;
    let (s, h) = symbol("endprimitive")(s)?;
    let (s, i) = opt(pair(symbol(":"), udp_identifier))(s)?;
    Ok((
        s,
        UdpDeclaration::Wildcard(UdpDeclarationWildcard {
            nodes: (a, b, c, d, e, f, g, h, i),
        }),
    ))
}
