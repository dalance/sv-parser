use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct InoutDeclaration<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<NetPortType<'a>>,
        ListOfPortIdentifiers<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum InputDeclaration<'a> {
    Net(InputDeclarationNet<'a>),
    Variable(InputDeclarationVariable<'a>),
}

#[derive(Debug, Node)]
pub struct InputDeclarationNet<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<NetPortType<'a>>,
        ListOfPortIdentifiers<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct InputDeclarationVariable<'a> {
    pub nodes: (
        Symbol<'a>,
        VariablePortType<'a>,
        ListOfVariableIdentifiers<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum OutputDeclaration<'a> {
    Net(OutputDeclarationNet<'a>),
    Variable(OutputDeclarationVariable<'a>),
}

#[derive(Debug, Node)]
pub struct OutputDeclarationNet<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<NetPortType<'a>>,
        ListOfPortIdentifiers<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct OutputDeclarationVariable<'a> {
    pub nodes: (
        Symbol<'a>,
        VariablePortType<'a>,
        ListOfVariableIdentifiers<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct InterfacePortDeclaration<'a> {
    pub nodes: (
        InterfaceIdentifier<'a>,
        Option<(Symbol<'a>, ModportIdentifier<'a>)>,
        ListOfInterfaceIdentifiers<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct RefDeclaration<'a> {
    pub nodes: (
        Symbol<'a>,
        VariablePortType<'a>,
        ListOfVariableIdentifiers<'a>,
    ),
}

// -----------------------------------------------------------------------------

#[parser(Ambiguous)]
pub fn inout_declaration(s: Span) -> IResult<Span, InoutDeclaration> {
    let (s, a) = symbol("inout")(s)?;
    let (s, b) = ambiguous_opt(net_port_type)(s)?;
    let (s, c) = list_of_port_identifiers(s)?;
    Ok((s, InoutDeclaration { nodes: (a, b, c) }))
}

#[parser]
pub fn input_declaration(s: Span) -> IResult<Span, InputDeclaration> {
    alt((input_declaration_net, input_declaration_variable))(s)
}

#[parser(Ambiguous)]
pub fn input_declaration_net(s: Span) -> IResult<Span, InputDeclaration> {
    let (s, a) = symbol("input")(s)?;
    let (s, b) = ambiguous_opt(net_port_type)(s)?;
    let (s, c) = list_of_port_identifiers(s)?;
    Ok((
        s,
        InputDeclaration::Net(InputDeclarationNet { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn input_declaration_variable(s: Span) -> IResult<Span, InputDeclaration> {
    let (s, a) = symbol("input")(s)?;
    let (s, b) = variable_port_type(s)?;
    let (s, c) = list_of_variable_identifiers(s)?;
    Ok((
        s,
        InputDeclaration::Variable(InputDeclarationVariable { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn output_declaration(s: Span) -> IResult<Span, OutputDeclaration> {
    alt((output_declaration_net, output_declaration_variable))(s)
}

#[parser(Ambiguous)]
pub fn output_declaration_net(s: Span) -> IResult<Span, OutputDeclaration> {
    let (s, a) = symbol("output")(s)?;
    let (s, b) = ambiguous_opt(net_port_type)(s)?;
    let (s, c) = list_of_port_identifiers(s)?;
    Ok((
        s,
        OutputDeclaration::Net(OutputDeclarationNet { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn output_declaration_variable(s: Span) -> IResult<Span, OutputDeclaration> {
    let (s, a) = symbol("output")(s)?;
    let (s, b) = variable_port_type(s)?;
    let (s, c) = list_of_variable_identifiers(s)?;
    Ok((
        s,
        OutputDeclaration::Variable(OutputDeclarationVariable { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn interface_port_declaration(s: Span) -> IResult<Span, InterfacePortDeclaration> {
    let (s, a) = interface_identifier(s)?;
    let (s, b) = opt(pair(symbol("."), modport_identifier))(s)?;
    let (s, c) = list_of_interface_identifiers(s)?;
    Ok((s, InterfacePortDeclaration { nodes: (a, b, c) }))
}

#[parser]
pub fn ref_declaration(s: Span) -> IResult<Span, RefDeclaration> {
    let (s, a) = symbol("ref")(s)?;
    let (s, b) = variable_port_type(s)?;
    let (s, c) = list_of_variable_identifiers(s)?;
    Ok((s, RefDeclaration { nodes: (a, b, c) }))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_inout_declaration() {
        parser_test!(inout_declaration, "inout a", Ok((_, _)));
        parser_test!(inout_declaration, "inout [7:0] a", Ok((_, _)));
        parser_test!(inout_declaration, "inout signed [7:0] a", Ok((_, _)));
        parser_test!(inout_declaration, "inout var a", Ok((_, _)));
    }
}
