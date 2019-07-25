use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct UdpNonansiDeclaration {
    pub nodes: (
        Vec<AttributeInstance>,
        Keyword,
        UdpIdentifier,
        Paren<UdpPortList>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct UdpAnsiDeclaration {
    pub nodes: (
        Vec<AttributeInstance>,
        Keyword,
        UdpIdentifier,
        Paren<UdpDeclarationPortList>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum UdpDeclaration {
    Nonansi(Box<UdpDeclarationNonansi>),
    Ansi(Box<UdpDeclarationAnsi>),
    ExternNonansi(Box<UdpDeclarationExternNonansi>),
    ExternAnsi(Box<UdpDeclarationExternAnsi>),
    Wildcard(Box<UdpDeclarationWildcard>),
}

#[derive(Clone, Debug, Node)]
pub struct UdpDeclarationNonansi {
    pub nodes: (
        UdpNonansiDeclaration,
        UdpPortDeclaration,
        Vec<UdpPortDeclaration>,
        UdpBody,
        Keyword,
        Option<(Symbol, UdpIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct UdpDeclarationAnsi {
    pub nodes: (
        UdpAnsiDeclaration,
        UdpBody,
        Keyword,
        Option<(Symbol, UdpIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct UdpDeclarationExternNonansi {
    pub nodes: (Keyword, UdpNonansiDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct UdpDeclarationExternAnsi {
    pub nodes: (Keyword, UdpAnsiDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct UdpDeclarationWildcard {
    pub nodes: (
        Vec<AttributeInstance>,
        Keyword,
        UdpIdentifier,
        Paren<Symbol>,
        Symbol,
        Vec<UdpPortDeclaration>,
        UdpBody,
        Keyword,
        Option<(Symbol, UdpIdentifier)>,
    ),
}

// -----------------------------------------------------------------------------

#[parser]
pub(crate) fn udp_nonansi_declaration(s: Span) -> IResult<Span, UdpNonansiDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = keyword("primitive")(s)?;
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
pub(crate) fn udp_ansi_declaration(s: Span) -> IResult<Span, UdpAnsiDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = keyword("primitive")(s)?;
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
pub(crate) fn udp_declaration(s: Span) -> IResult<Span, UdpDeclaration> {
    alt((
        udp_declaration_nonansi,
        udp_declaration_ansi,
        udp_declaration_extern_nonansi,
        udp_declaration_extern_ansi,
        udp_declaration_wildcard,
    ))(s)
}

#[parser]
pub(crate) fn udp_declaration_nonansi(s: Span) -> IResult<Span, UdpDeclaration> {
    let (s, a) = udp_nonansi_declaration(s)?;
    let (s, b) = udp_port_declaration(s)?;
    let (s, c) = many0(udp_port_declaration)(s)?;
    let (s, d) = udp_body(s)?;
    let (s, e) = keyword("endprimitive")(s)?;
    let (s, f) = opt(pair(symbol(":"), udp_identifier))(s)?;
    Ok((
        s,
        UdpDeclaration::Nonansi(Box::new(UdpDeclarationNonansi {
            nodes: (a, b, c, d, e, f),
        })),
    ))
}

#[parser]
pub(crate) fn udp_declaration_ansi(s: Span) -> IResult<Span, UdpDeclaration> {
    let (s, a) = udp_ansi_declaration(s)?;
    let (s, b) = udp_body(s)?;
    let (s, c) = keyword("endprimitive")(s)?;
    let (s, d) = opt(pair(symbol(":"), udp_identifier))(s)?;
    Ok((
        s,
        UdpDeclaration::Ansi(Box::new(UdpDeclarationAnsi {
            nodes: (a, b, c, d),
        })),
    ))
}

#[parser]
pub(crate) fn udp_declaration_extern_nonansi(s: Span) -> IResult<Span, UdpDeclaration> {
    let (s, a) = keyword("extern")(s)?;
    let (s, b) = udp_nonansi_declaration(s)?;
    Ok((
        s,
        UdpDeclaration::ExternNonansi(Box::new(UdpDeclarationExternNonansi { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn udp_declaration_extern_ansi(s: Span) -> IResult<Span, UdpDeclaration> {
    let (s, a) = keyword("extern")(s)?;
    let (s, b) = udp_ansi_declaration(s)?;
    Ok((
        s,
        UdpDeclaration::ExternAnsi(Box::new(UdpDeclarationExternAnsi { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn udp_declaration_wildcard(s: Span) -> IResult<Span, UdpDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = keyword("primitive")(s)?;
    let (s, c) = udp_identifier(s)?;
    let (s, d) = paren(symbol(".*"))(s)?;
    let (s, e) = symbol(";")(s)?;
    let (s, f) = many0(udp_port_declaration)(s)?;
    let (s, g) = udp_body(s)?;
    let (s, h) = keyword("endprimitive")(s)?;
    let (s, i) = opt(pair(symbol(":"), udp_identifier))(s)?;
    Ok((
        s,
        UdpDeclaration::Wildcard(Box::new(UdpDeclarationWildcard {
            nodes: (a, b, c, d, e, f, g, h, i),
        })),
    ))
}
