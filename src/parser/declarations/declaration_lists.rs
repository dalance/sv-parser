use crate::ast::*;
use crate::parser::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct ListOfDefparamAssignments {
    pub nodes: (List<Symbol, DefparamAssignment>,),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfGenvarIdentifiers {
    pub nodes: (List<Symbol, GenvarIdentifier>,),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfInterfaceIdentifiers {
    pub nodes: (List<Symbol, (InterfaceIdentifier, Vec<UnpackedDimension>)>,),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfNetDeclAssignments {
    pub nodes: (List<Symbol, NetDeclAssignment>,),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfParamAssignments {
    pub nodes: (List<Symbol, ParamAssignment>,),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfPortIdentifiers {
    pub nodes: (List<Symbol, (PortIdentifier, Vec<UnpackedDimension>)>,),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfUdpPortIdentifiers {
    pub nodes: (List<Symbol, PortIdentifier>,),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfSpecparamAssignments {
    pub nodes: (List<Symbol, SpecparamAssignment>,),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfTfVariableIdentifiers {
    pub nodes: (
        List<
            Symbol,
            (
                PortIdentifier,
                Vec<VariableDimension>,
                Option<(Symbol, Expression)>,
            ),
        >,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfTypeAssignments {
    pub nodes: (List<Symbol, TypeAssignment>,),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfVariableDeclAssignments {
    pub nodes: (List<Symbol, VariableDeclAssignment>,),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfVariableIdentifiers {
    pub nodes: (List<Symbol, (VariableIdentifier, Vec<VariableDimension>)>,),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfVariablePortIdentifiers {
    pub nodes: (
        List<
            Symbol,
            (
                PortIdentifier,
                Vec<VariableDimension>,
                Option<(Symbol, ConstantExpression)>,
            ),
        >,
    ),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn list_of_defparam_assignments(s: Span) -> IResult<Span, ListOfDefparamAssignments> {
    let (s, a) = list(symbol(","), defparam_assignment)(s)?;
    Ok((s, ListOfDefparamAssignments { nodes: (a,) }))
}

#[parser]
pub fn list_of_genvar_identifiers(s: Span) -> IResult<Span, ListOfGenvarIdentifiers> {
    let (s, a) = list(symbol(","), genvar_identifier)(s)?;
    Ok((s, ListOfGenvarIdentifiers { nodes: (a,) }))
}

#[parser]
pub fn list_of_interface_identifiers(s: Span) -> IResult<Span, ListOfInterfaceIdentifiers> {
    let (s, a) = list(
        symbol(","),
        pair(interface_identifier, many0(unpacked_dimension)),
    )(s)?;
    Ok((s, ListOfInterfaceIdentifiers { nodes: (a,) }))
}

#[parser]
pub fn list_of_net_decl_assignments(s: Span) -> IResult<Span, ListOfNetDeclAssignments> {
    let (s, a) = list(symbol(","), net_decl_assignment)(s)?;
    Ok((s, ListOfNetDeclAssignments { nodes: (a,) }))
}

#[parser]
pub fn list_of_param_assignments(s: Span) -> IResult<Span, ListOfParamAssignments> {
    let (s, a) = list(symbol(","), param_assignment)(s)?;
    Ok((s, ListOfParamAssignments { nodes: (a,) }))
}

#[parser]
pub fn list_of_port_identifiers(s: Span) -> IResult<Span, ListOfPortIdentifiers> {
    let (s, a) = list(
        symbol(","),
        pair(port_identifier, many0(unpacked_dimension)),
    )(s)?;
    Ok((s, ListOfPortIdentifiers { nodes: (a,) }))
}

#[parser]
pub fn list_of_udp_port_identifiers(s: Span) -> IResult<Span, ListOfUdpPortIdentifiers> {
    let (s, a) = list(symbol(","), port_identifier)(s)?;
    Ok((s, ListOfUdpPortIdentifiers { nodes: (a,) }))
}

#[parser]
pub fn list_of_specparam_assignments(s: Span) -> IResult<Span, ListOfSpecparamAssignments> {
    let (s, a) = list(symbol(","), specparam_assignment)(s)?;
    Ok((s, ListOfSpecparamAssignments { nodes: (a,) }))
}

#[parser]
pub fn list_of_tf_variable_identifiers(s: Span) -> IResult<Span, ListOfTfVariableIdentifiers> {
    let (s, a) = list(
        symbol(","),
        triple(
            port_identifier,
            many0(variable_dimension),
            opt(pair(symbol("="), expression)),
        ),
    )(s)?;
    Ok((s, ListOfTfVariableIdentifiers { nodes: (a,) }))
}

#[parser]
pub fn list_of_type_assignments(s: Span) -> IResult<Span, ListOfTypeAssignments> {
    let (s, a) = list(symbol(","), type_assignment)(s)?;
    Ok((s, ListOfTypeAssignments { nodes: (a,) }))
}

#[parser]
pub fn list_of_variable_decl_assignments(s: Span) -> IResult<Span, ListOfVariableDeclAssignments> {
    let (s, a) = list(symbol(","), variable_decl_assignment)(s)?;
    Ok((s, ListOfVariableDeclAssignments { nodes: (a,) }))
}

#[parser]
pub fn list_of_variable_identifiers(s: Span) -> IResult<Span, ListOfVariableIdentifiers> {
    let (s, a) = list(
        symbol(","),
        pair(variable_identifier, many0(variable_dimension)),
    )(s)?;
    Ok((s, ListOfVariableIdentifiers { nodes: (a,) }))
}

#[parser]
pub fn list_of_variable_port_identifiers(s: Span) -> IResult<Span, ListOfVariablePortIdentifiers> {
    let (s, a) = list(
        symbol(","),
        triple(
            port_identifier,
            many0(variable_dimension),
            opt(pair(symbol("="), constant_expression)),
        ),
    )(s)?;
    Ok((s, ListOfVariablePortIdentifiers { nodes: (a,) }))
}
