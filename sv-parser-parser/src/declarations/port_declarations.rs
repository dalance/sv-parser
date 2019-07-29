use crate::*;

// -----------------------------------------------------------------------------

#[both_parser]
#[tracable_parser]
pub(crate) fn inout_declaration(s: Span) -> IResult<Span, InoutDeclaration> {
    let (s, a) = keyword("inout")(s)?;
    let (s, b) = both_opt(net_port_type)(s)?;
    let (s, c) = list_of_port_identifiers(s)?;
    Ok((s, InoutDeclaration { nodes: (a, b, c) }))
}

#[tracable_parser]
pub(crate) fn input_declaration(s: Span) -> IResult<Span, InputDeclaration> {
    alt((input_declaration_net, input_declaration_variable))(s)
}

#[both_parser]
#[tracable_parser]
pub(crate) fn input_declaration_net(s: Span) -> IResult<Span, InputDeclaration> {
    let (s, a) = keyword("input")(s)?;
    let (s, b) = both_opt(net_port_type)(s)?;
    let (s, c) = list_of_port_identifiers(s)?;
    Ok((
        s,
        InputDeclaration::Net(Box::new(InputDeclarationNet { nodes: (a, b, c) })),
    ))
}

#[both_parser]
#[tracable_parser]
pub(crate) fn input_declaration_variable(s: Span) -> IResult<Span, InputDeclaration> {
    let (s, a) = keyword("input")(s)?;
    let (s, b) = both_alt(variable_port_type, implicit_var)(s)?;
    let (s, c) = list_of_variable_identifiers(s)?;
    Ok((
        s,
        InputDeclaration::Variable(Box::new(InputDeclarationVariable { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn output_declaration(s: Span) -> IResult<Span, OutputDeclaration> {
    alt((output_declaration_net, output_declaration_variable))(s)
}

#[both_parser]
#[tracable_parser]
pub(crate) fn output_declaration_net(s: Span) -> IResult<Span, OutputDeclaration> {
    let (s, a) = keyword("output")(s)?;
    let (s, b) = both_opt(net_port_type)(s)?;
    let (s, c) = list_of_port_identifiers(s)?;
    Ok((
        s,
        OutputDeclaration::Net(Box::new(OutputDeclarationNet { nodes: (a, b, c) })),
    ))
}

#[both_parser]
#[tracable_parser]
pub(crate) fn output_declaration_variable(s: Span) -> IResult<Span, OutputDeclaration> {
    let (s, a) = keyword("output")(s)?;
    let (s, b) = both_alt(variable_port_type, implicit_var)(s)?;
    let (s, c) = list_of_variable_port_identifiers(s)?;
    Ok((
        s,
        OutputDeclaration::Variable(Box::new(OutputDeclarationVariable { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn interface_port_declaration(s: Span) -> IResult<Span, InterfacePortDeclaration> {
    let (s, a) = interface_identifier(s)?;
    let (s, b) = opt(pair(symbol("."), modport_identifier))(s)?;
    let (s, c) = list_of_interface_identifiers(s)?;
    Ok((s, InterfacePortDeclaration { nodes: (a, b, c) }))
}

#[both_parser]
#[tracable_parser]
pub(crate) fn ref_declaration(s: Span) -> IResult<Span, RefDeclaration> {
    let (s, a) = keyword("ref")(s)?;
    let (s, b) = both_alt(variable_port_type, implicit_var)(s)?;
    let (s, c) = list_of_variable_identifiers(s)?;
    Ok((s, RefDeclaration { nodes: (a, b, c) }))
}

#[tracable_parser]
pub(crate) fn implicit_var(s: Span) -> IResult<Span, VariablePortType> {
    let (s, a) = keyword("var")(s)?;
    Ok((
        s,
        VariablePortType {
            nodes: (VarDataType::Var(Box::new(VarDataTypeVar {
                nodes: (
                    a,
                    DataTypeOrImplicit::ImplicitDataType(Box::new(ImplicitDataType {
                        nodes: (None, vec![]),
                    })),
                ),
            })),),
        },
    ))
}
