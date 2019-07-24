use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct InoutDeclaration {
    pub nodes: (Keyword, Option<NetPortType>, ListOfPortIdentifiers),
}

#[derive(Clone, Debug, Node)]
pub enum InputDeclaration {
    Net(Box<InputDeclarationNet>),
    Variable(Box<InputDeclarationVariable>),
}

#[derive(Clone, Debug, Node)]
pub struct InputDeclarationNet {
    pub nodes: (Keyword, Option<NetPortType>, ListOfPortIdentifiers),
}

#[derive(Clone, Debug, Node)]
pub struct InputDeclarationVariable {
    pub nodes: (Keyword, VariablePortType, ListOfVariableIdentifiers),
}

#[derive(Clone, Debug, Node)]
pub enum OutputDeclaration {
    Net(Box<OutputDeclarationNet>),
    Variable(Box<OutputDeclarationVariable>),
}

#[derive(Clone, Debug, Node)]
pub struct OutputDeclarationNet {
    pub nodes: (Keyword, Option<NetPortType>, ListOfPortIdentifiers),
}

#[derive(Clone, Debug, Node)]
pub struct OutputDeclarationVariable {
    pub nodes: (Keyword, VariablePortType, ListOfVariableIdentifiers),
}

#[derive(Clone, Debug, Node)]
pub struct InterfacePortDeclaration {
    pub nodes: (
        InterfaceIdentifier,
        Option<(Symbol, ModportIdentifier)>,
        ListOfInterfaceIdentifiers,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct RefDeclaration {
    pub nodes: (Keyword, VariablePortType, ListOfVariableIdentifiers),
}

// -----------------------------------------------------------------------------

#[parser(Ambiguous)]
pub fn inout_declaration(s: Span) -> IResult<Span, InoutDeclaration> {
    let (s, a) = keyword("inout")(s)?;
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
    let (s, a) = keyword("input")(s)?;
    let (s, b) = ambiguous_opt(net_port_type)(s)?;
    let (s, c) = list_of_port_identifiers(s)?;
    Ok((
        s,
        InputDeclaration::Net(Box::new(InputDeclarationNet { nodes: (a, b, c) })),
    ))
}

#[parser(Ambiguous)]
pub fn input_declaration_variable(s: Span) -> IResult<Span, InputDeclaration> {
    let (s, a) = keyword("input")(s)?;
    let (s, b) = ambiguous_alt(variable_port_type, implicit_var)(s)?;
    let (s, c) = list_of_variable_identifiers(s)?;
    Ok((
        s,
        InputDeclaration::Variable(Box::new(InputDeclarationVariable { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn output_declaration(s: Span) -> IResult<Span, OutputDeclaration> {
    alt((output_declaration_net, output_declaration_variable))(s)
}

#[parser(Ambiguous)]
pub fn output_declaration_net(s: Span) -> IResult<Span, OutputDeclaration> {
    let (s, a) = keyword("output")(s)?;
    let (s, b) = ambiguous_opt(net_port_type)(s)?;
    let (s, c) = list_of_port_identifiers(s)?;
    Ok((
        s,
        OutputDeclaration::Net(Box::new(OutputDeclarationNet { nodes: (a, b, c) })),
    ))
}

#[parser(Ambiguous)]
pub fn output_declaration_variable(s: Span) -> IResult<Span, OutputDeclaration> {
    let (s, a) = keyword("output")(s)?;
    let (s, b) = ambiguous_alt(variable_port_type, implicit_var)(s)?;
    let (s, c) = list_of_variable_identifiers(s)?;
    Ok((
        s,
        OutputDeclaration::Variable(Box::new(OutputDeclarationVariable { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn interface_port_declaration(s: Span) -> IResult<Span, InterfacePortDeclaration> {
    let (s, a) = interface_identifier(s)?;
    let (s, b) = opt(pair(symbol("."), modport_identifier))(s)?;
    let (s, c) = list_of_interface_identifiers(s)?;
    Ok((s, InterfacePortDeclaration { nodes: (a, b, c) }))
}

#[parser(Ambiguous)]
pub fn ref_declaration(s: Span) -> IResult<Span, RefDeclaration> {
    let (s, a) = keyword("ref")(s)?;
    let (s, b) = ambiguous_alt(variable_port_type, implicit_var)(s)?;
    let (s, c) = list_of_variable_identifiers(s)?;
    Ok((s, RefDeclaration { nodes: (a, b, c) }))
}

#[parser]
pub fn implicit_var(s: Span) -> IResult<Span, VariablePortType> {
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

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_inout_declaration() {
        parser_test!(inout_declaration, "inout a", Ok((_, _)));
        parser_test!(inout_declaration, "inout [7:0] a", Ok((_, _)));
        parser_test!(inout_declaration, "inout signed [7:0] a", Ok((_, _)));
    }
}
