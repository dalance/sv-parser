use crate::ast::*;
use crate::parser::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct ListOfDefparamAssignments<'a> {
    pub nodes: (List<Symbol<'a>, DefparamAssignment<'a>>,),
}

#[derive(Debug, Node)]
pub struct ListOfGenvarIdentifiers<'a> {
    pub nodes: (List<Symbol<'a>, GenvarIdentifier<'a>>,),
}

#[derive(Debug, Node)]
pub struct ListOfInterfaceIdentifiers<'a> {
    pub nodes: (List<Symbol<'a>, (InterfaceIdentifier<'a>, Vec<UnpackedDimension<'a>>)>,),
}

#[derive(Debug, Node)]
pub struct ListOfNetDeclAssignments<'a> {
    pub nodes: (List<Symbol<'a>, NetDeclAssignment<'a>>,),
}

#[derive(Debug, Node)]
pub struct ListOfParamAssignments<'a> {
    pub nodes: (List<Symbol<'a>, ParamAssignment<'a>>,),
}

#[derive(Debug, Node)]
pub struct ListOfPortIdentifiers<'a> {
    pub nodes: (List<Symbol<'a>, (PortIdentifier<'a>, Vec<UnpackedDimension<'a>>)>,),
}

#[derive(Debug, Node)]
pub struct ListOfUdpPortIdentifiers<'a> {
    pub nodes: (List<Symbol<'a>, PortIdentifier<'a>>,),
}

#[derive(Debug, Node)]
pub struct ListOfSpecparamAssignments<'a> {
    pub nodes: (List<Symbol<'a>, SpecparamAssignment<'a>>,),
}

#[derive(Debug, Node)]
pub struct ListOfTfVariableIdentifiers<'a> {
    pub nodes: (
        List<
            Symbol<'a>,
            (
                PortIdentifier<'a>,
                Vec<VariableDimension<'a>>,
                Option<(Symbol<'a>, Expression<'a>)>,
            ),
        >,
    ),
}

#[derive(Debug, Node)]
pub struct ListOfTypeAssignments<'a> {
    pub nodes: (List<Symbol<'a>, TypeAssignment<'a>>,),
}

#[derive(Debug, Node)]
pub struct ListOfVariableDeclAssignments<'a> {
    pub nodes: (List<Symbol<'a>, VariableDeclAssignment<'a>>,),
}

#[derive(Debug, Node)]
pub struct ListOfVariableIdentifiers<'a> {
    pub nodes: (List<Symbol<'a>, (VariableIdentifier<'a>, Vec<VariableDimension<'a>>)>,),
}

#[derive(Debug, Node)]
pub struct ListOfVariablePortIdentifiers<'a> {
    pub nodes: (
        List<
            Symbol<'a>,
            (
                PortIdentifier<'a>,
                Vec<VariableDimension<'a>>,
                Option<(Symbol<'a>, ConstantExpression<'a>)>,
            ),
        >,
    ),
}

// -----------------------------------------------------------------------------

#[trace]
pub fn list_of_defparam_assignments(s: Span) -> IResult<Span, ListOfDefparamAssignments> {
    let (s, a) = list(symbol(","), defparam_assignment)(s)?;
    Ok((s, ListOfDefparamAssignments { nodes: (a,) }))
}

#[trace]
pub fn list_of_genvar_identifiers(s: Span) -> IResult<Span, ListOfGenvarIdentifiers> {
    let (s, a) = list(symbol(","), genvar_identifier)(s)?;
    Ok((s, ListOfGenvarIdentifiers { nodes: (a,) }))
}

#[trace]
pub fn list_of_interface_identifiers(s: Span) -> IResult<Span, ListOfInterfaceIdentifiers> {
    let (s, a) = list(
        symbol(","),
        pair(interface_identifier, many0(unpacked_dimension)),
    )(s)?;
    Ok((s, ListOfInterfaceIdentifiers { nodes: (a,) }))
}

#[trace]
pub fn list_of_net_decl_assignments(s: Span) -> IResult<Span, ListOfNetDeclAssignments> {
    let (s, a) = list(symbol(","), net_decl_assignment)(s)?;
    Ok((s, ListOfNetDeclAssignments { nodes: (a,) }))
}

#[trace]
pub fn list_of_param_assignments(s: Span) -> IResult<Span, ListOfParamAssignments> {
    let (s, a) = list(symbol(","), param_assignment)(s)?;
    Ok((s, ListOfParamAssignments { nodes: (a,) }))
}

#[trace]
pub fn list_of_port_identifiers(s: Span) -> IResult<Span, ListOfPortIdentifiers> {
    let (s, a) = list(
        symbol(","),
        pair(port_identifier, many0(unpacked_dimension)),
    )(s)?;
    Ok((s, ListOfPortIdentifiers { nodes: (a,) }))
}

#[trace]
pub fn list_of_udp_port_identifiers(s: Span) -> IResult<Span, ListOfUdpPortIdentifiers> {
    let (s, a) = list(symbol(","), port_identifier)(s)?;
    Ok((s, ListOfUdpPortIdentifiers { nodes: (a,) }))
}

#[trace]
pub fn list_of_specparam_assignments(s: Span) -> IResult<Span, ListOfSpecparamAssignments> {
    let (s, a) = list(symbol(","), specparam_assignment)(s)?;
    Ok((s, ListOfSpecparamAssignments { nodes: (a,) }))
}

#[trace]
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

#[trace]
pub fn list_of_type_assignments(s: Span) -> IResult<Span, ListOfTypeAssignments> {
    let (s, a) = list(symbol(","), type_assignment)(s)?;
    Ok((s, ListOfTypeAssignments { nodes: (a,) }))
}

#[trace]
pub fn list_of_variable_decl_assignments(s: Span) -> IResult<Span, ListOfVariableDeclAssignments> {
    let (s, a) = list(symbol(","), variable_decl_assignment)(s)?;
    Ok((s, ListOfVariableDeclAssignments { nodes: (a,) }))
}

#[trace]
pub fn list_of_variable_identifiers(s: Span) -> IResult<Span, ListOfVariableIdentifiers> {
    let (s, a) = list(
        symbol(","),
        pair(variable_identifier, many0(variable_dimension)),
    )(s)?;
    Ok((s, ListOfVariableIdentifiers { nodes: (a,) }))
}

#[trace]
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
