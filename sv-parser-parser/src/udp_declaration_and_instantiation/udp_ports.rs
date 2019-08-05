use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn udp_port_list(s: Span) -> IResult<Span, UdpPortList> {
    let (s, a) = output_port_identifier(s)?;
    let (s, b) = symbol(",")(s)?;
    let (s, c) = list(symbol(","), input_port_identifier)(s)?;
    Ok((s, UdpPortList { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn udp_declaration_port_list(s: Span) -> IResult<Span, UdpDeclarationPortList> {
    let (s, a) = udp_output_declaration(s)?;
    let (s, b) = symbol(",")(s)?;
    let (s, c) = list(symbol(","), udp_input_declaration)(s)?;
    Ok((s, UdpDeclarationPortList { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn udp_port_declaration(s: Span) -> IResult<Span, UdpPortDeclaration> {
    alt((
        map(pair(udp_output_declaration, symbol(";")), |x| {
            UdpPortDeclaration::UdpOutputDeclaration(Box::new(x))
        }),
        map(pair(udp_input_declaration, symbol(";")), |x| {
            UdpPortDeclaration::UdpInputDeclaration(Box::new(x))
        }),
        map(pair(udp_reg_declaration, symbol(";")), |x| {
            UdpPortDeclaration::UdpRegDeclaration(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn udp_output_declaration(s: Span) -> IResult<Span, UdpOutputDeclaration> {
    alt((udp_output_declaration_nonreg, udp_output_declaration_reg))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn udp_output_declaration_nonreg(s: Span) -> IResult<Span, UdpOutputDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = keyword("output")(s)?;
    let (s, c) = port_identifier(s)?;
    Ok((
        s,
        UdpOutputDeclaration::Nonreg(Box::new(UdpOutputDeclarationNonreg { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn udp_output_declaration_reg(s: Span) -> IResult<Span, UdpOutputDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = keyword("output")(s)?;
    let (s, c) = keyword("reg")(s)?;
    let (s, d) = port_identifier(s)?;
    let (s, e) = opt(pair(symbol("="), constant_expression))(s)?;
    Ok((
        s,
        UdpOutputDeclaration::Reg(Box::new(UdpOutputDeclarationReg {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn udp_input_declaration(s: Span) -> IResult<Span, UdpInputDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = keyword("input")(s)?;
    let (s, c) = list_of_udp_port_identifiers(s)?;
    Ok((s, UdpInputDeclaration { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn udp_reg_declaration(s: Span) -> IResult<Span, UdpRegDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = keyword("reg")(s)?;
    let (s, c) = variable_identifier(s)?;
    Ok((s, UdpRegDeclaration { nodes: (a, b, c) }))
}
