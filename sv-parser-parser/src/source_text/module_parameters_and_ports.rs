use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn parameter_port_list(s: Span) -> IResult<Span, ParameterPortList> {
    alt((
        parameter_port_list_assignment,
        parameter_port_list_declaration,
        parameter_port_list_empty,
    ))(s)
}

#[tracable_parser]
pub(crate) fn parameter_port_list_assignment(s: Span) -> IResult<Span, ParameterPortList> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = paren(pair(
        list_of_param_assignments,
        many0(pair(symbol(","), parameter_port_declaration)),
    ))(s)?;
    Ok((
        s,
        ParameterPortList::Assignment(Box::new(ParameterPortListAssignment { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn parameter_port_list_declaration(s: Span) -> IResult<Span, ParameterPortList> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = paren(list(symbol(","), parameter_port_declaration))(s)?;
    Ok((
        s,
        ParameterPortList::Declaration(Box::new(ParameterPortListDeclaration { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn parameter_port_list_empty(s: Span) -> IResult<Span, ParameterPortList> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = symbol("(")(s)?;
    let (s, c) = symbol(")")(s)?;
    Ok((s, ParameterPortList::Empty(Box::new((a, b, c)))))
}

#[tracable_parser]
pub(crate) fn parameter_port_declaration(s: Span) -> IResult<Span, ParameterPortDeclaration> {
    alt((
        map(parameter_declaration, |x| {
            ParameterPortDeclaration::ParameterDeclaration(Box::new(x))
        }),
        map(local_parameter_declaration, |x| {
            ParameterPortDeclaration::LocalParameterDeclaration(Box::new(x))
        }),
        parameter_port_declaration_param_list,
        parameter_port_declaration_type_list,
    ))(s)
}

#[tracable_parser]
pub(crate) fn parameter_port_declaration_param_list(
    s: Span,
) -> IResult<Span, ParameterPortDeclaration> {
    let (s, a) = data_type(s)?;
    let (s, b) = list_of_param_assignments(s)?;
    Ok((
        s,
        ParameterPortDeclaration::ParamList(Box::new(ParameterPortDeclarationParamList {
            nodes: (a, b),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn parameter_port_declaration_type_list(
    s: Span,
) -> IResult<Span, ParameterPortDeclaration> {
    let (s, a) = keyword("type")(s)?;
    let (s, b) = list_of_type_assignments(s)?;
    Ok((
        s,
        ParameterPortDeclaration::TypeList(Box::new(ParameterPortDeclarationTypeList {
            nodes: (a, b),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn list_of_ports(s: Span) -> IResult<Span, ListOfPorts> {
    let (s, a) = paren(list(symbol(","), port))(s)?;
    Ok((s, ListOfPorts { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn list_of_port_declarations(s: Span) -> IResult<Span, ListOfPortDeclarations> {
    let (s, a) = paren(opt(list(
        symbol(","),
        pair(many0(attribute_instance), ansi_port_declaration),
    )))(s)?;
    Ok((s, ListOfPortDeclarations { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn port_declaration(s: Span) -> IResult<Span, PortDeclaration> {
    alt((
        port_declaration_inout,
        port_declaration_input,
        port_declaration_output,
        port_declaration_ref,
        port_declaration_interface,
    ))(s)
}

#[tracable_parser]
pub(crate) fn port_declaration_inout(s: Span) -> IResult<Span, PortDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = inout_declaration(s)?;
    Ok((
        s,
        PortDeclaration::Inout(Box::new(PortDeclarationInout { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn port_declaration_input(s: Span) -> IResult<Span, PortDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = input_declaration(s)?;
    Ok((
        s,
        PortDeclaration::Input(Box::new(PortDeclarationInput { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn port_declaration_output(s: Span) -> IResult<Span, PortDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = output_declaration(s)?;
    Ok((
        s,
        PortDeclaration::Output(Box::new(PortDeclarationOutput { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn port_declaration_ref(s: Span) -> IResult<Span, PortDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = ref_declaration(s)?;
    Ok((
        s,
        PortDeclaration::Ref(Box::new(PortDeclarationRef { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn port_declaration_interface(s: Span) -> IResult<Span, PortDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = interface_port_declaration(s)?;
    Ok((
        s,
        PortDeclaration::Interface(Box::new(PortDeclarationInterface { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn port(s: Span) -> IResult<Span, Port> {
    alt((port_non_named, port_named))(s)
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn port_non_named(s: Span) -> IResult<Span, Port> {
    let (s, a) = opt(port_expression)(s)?;
    Ok((s, Port::NonNamed(Box::new(PortNonNamed { nodes: (a,) }))))
}

#[tracable_parser]
pub(crate) fn port_named(s: Span) -> IResult<Span, Port> {
    let (s, a) = symbol(".")(s)?;
    let (s, b) = port_identifier(s)?;
    let (s, c) = paren(opt(port_expression))(s)?;
    Ok((s, Port::Named(Box::new(PortNamed { nodes: (a, b, c) }))))
}

#[tracable_parser]
pub(crate) fn port_expression(s: Span) -> IResult<Span, PortExpression> {
    alt((
        map(port_reference, |x| {
            PortExpression::PortReference(Box::new(x))
        }),
        port_expressio_named,
    ))(s)
}

#[tracable_parser]
pub(crate) fn port_expressio_named(s: Span) -> IResult<Span, PortExpression> {
    let (s, a) = brace(list(symbol(","), port_reference))(s)?;
    Ok((
        s,
        PortExpression::Brace(Box::new(PortExpressionBrace { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn port_reference(s: Span) -> IResult<Span, PortReference> {
    let (s, a) = port_identifier(s)?;
    let (s, b) = constant_select(s)?;
    Ok((s, PortReference { nodes: (a, b) }))
}

#[tracable_parser]
pub(crate) fn port_direction(s: Span) -> IResult<Span, PortDirection> {
    alt((
        map(keyword("input"), |x| PortDirection::Input(Box::new(x))),
        map(keyword("output"), |x| PortDirection::Output(Box::new(x))),
        map(keyword("inout"), |x| PortDirection::Inout(Box::new(x))),
        map(keyword("ref"), |x| PortDirection::Ref(Box::new(x))),
    ))(s)
}

#[tracable_parser]
pub(crate) fn net_port_header(s: Span) -> IResult<Span, NetPortHeader> {
    let (s, a) = opt(port_direction)(s)?;
    let (s, b) = net_port_type(s)?;
    Ok((s, NetPortHeader { nodes: (a, b) }))
}

#[tracable_parser]
pub(crate) fn variable_port_header(s: Span) -> IResult<Span, VariablePortHeader> {
    let (s, a) = opt(port_direction)(s)?;
    let (s, b) = variable_port_type(s)?;
    Ok((s, VariablePortHeader { nodes: (a, b) }))
}

#[tracable_parser]
pub(crate) fn interface_port_header(s: Span) -> IResult<Span, InterfacePortHeader> {
    alt((
        interface_port_header_identifier,
        interface_port_header_interface,
    ))(s)
}

#[tracable_parser]
pub(crate) fn interface_port_header_identifier(s: Span) -> IResult<Span, InterfacePortHeader> {
    let (s, a) = interface_identifier(s)?;
    let (s, b) = opt(pair(symbol("."), modport_identifier))(s)?;
    Ok((
        s,
        InterfacePortHeader::Identifier(Box::new(InterfacePortHeaderIdentifier { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn interface_port_header_interface(s: Span) -> IResult<Span, InterfacePortHeader> {
    let (s, a) = keyword("interface")(s)?;
    let (s, b) = opt(pair(symbol("."), modport_identifier))(s)?;
    Ok((
        s,
        InterfacePortHeader::Interface(Box::new(InterfacePortHeaderInterface { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn ansi_port_declaration(s: Span) -> IResult<Span, AnsiPortDeclaration> {
    alt((
        ansi_port_declaration_net,
        ansi_port_declaration_port,
        ansi_port_declaration_paren,
    ))(s)
}

#[tracable_parser]
pub(crate) fn ansi_port_declaration_net(s: Span) -> IResult<Span, AnsiPortDeclaration> {
    let (s, a) = opt(net_port_header_or_interface_port_header)(s)?;
    let (s, b) = port_identifier(s)?;
    let (s, c) = many0(unpacked_dimension)(s)?;
    let (s, d) = opt(pair(symbol("="), constant_expression))(s)?;
    Ok((
        s,
        AnsiPortDeclaration::Net(Box::new(AnsiPortDeclarationNet {
            nodes: (a, b, c, d),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn net_port_header_or_interface_port_header(
    s: Span,
) -> IResult<Span, NetPortHeaderOrInterfacePortHeader> {
    alt((
        map(net_port_header, |x| {
            NetPortHeaderOrInterfacePortHeader::NetPortHeader(Box::new(x))
        }),
        map(interface_port_header, |x| {
            NetPortHeaderOrInterfacePortHeader::InterfacePortHeader(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn ansi_port_declaration_port(s: Span) -> IResult<Span, AnsiPortDeclaration> {
    let (s, a) = opt(variable_port_header)(s)?;
    let (s, b) = port_identifier(s)?;
    let (s, c) = many0(variable_dimension)(s)?;
    let (s, d) = opt(pair(symbol("="), constant_expression))(s)?;
    Ok((
        s,
        AnsiPortDeclaration::Variable(Box::new(AnsiPortDeclarationVariable {
            nodes: (a, b, c, d),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn ansi_port_declaration_paren(s: Span) -> IResult<Span, AnsiPortDeclaration> {
    let (s, a) = opt(port_direction)(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = port_identifier(s)?;
    let (s, d) = paren(opt(expression))(s)?;
    Ok((
        s,
        AnsiPortDeclaration::Paren(Box::new(AnsiPortDeclarationParen {
            nodes: (a, b, c, d),
        })),
    ))
}
