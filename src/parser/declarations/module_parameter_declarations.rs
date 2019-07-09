use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum LocalParameterDeclaration<'a> {
    Param(LocalParameterDeclarationParam<'a>),
    Type(LocalParameterDeclarationType<'a>),
}

#[derive(Debug)]
pub struct LocalParameterDeclarationParam<'a> {
    pub nodes: (DataTypeOrImplicit<'a>, ListOfParamAssignments<'a>),
}

#[derive(Debug)]
pub struct LocalParameterDeclarationType<'a> {
    pub nodes: (ListOfTypeAssignments<'a>,),
}

#[derive(Debug)]
pub enum ParameterDeclaration<'a> {
    Param(ParameterDeclarationParam<'a>),
    Type(ParameterDeclarationType<'a>),
}

#[derive(Debug)]
pub struct ParameterDeclarationParam<'a> {
    pub nodes: (DataTypeOrImplicit<'a>, ListOfParamAssignments<'a>),
}

#[derive(Debug)]
pub struct ParameterDeclarationType<'a> {
    pub nodes: (ListOfTypeAssignments<'a>,),
}

#[derive(Debug)]
pub struct SpecparamDeclaration<'a> {
    pub nodes: (Option<PackedDimension<'a>>, ListOfSpecparamAssignments<'a>),
}

// -----------------------------------------------------------------------------

pub fn local_parameter_declaration(s: Span) -> IResult<Span, LocalParameterDeclaration> {
    alt((
        local_parameter_declaration_param,
        local_parameter_declaration_type,
    ))(s)
}

pub fn local_parameter_declaration_param(s: Span) -> IResult<Span, LocalParameterDeclaration> {
    let (s, _) = symbol("localparam")(s)?;
    let (s, x) = data_type_or_implicit(s)?;
    let (s, y) = list_of_param_assignments(s)?;
    Ok((
        s,
        LocalParameterDeclaration::Param(LocalParameterDeclarationParam { nodes: (x, y) }),
    ))
}

pub fn local_parameter_declaration_type(s: Span) -> IResult<Span, LocalParameterDeclaration> {
    let (s, _) = symbol("localparam")(s)?;
    let (s, _) = symbol("type")(s)?;
    let (s, x) = list_of_type_assignments(s)?;
    Ok((
        s,
        LocalParameterDeclaration::Type(LocalParameterDeclarationType { nodes: (x,) }),
    ))
}

pub fn parameter_declaration(s: Span) -> IResult<Span, ParameterDeclaration> {
    alt((parameter_declaration_param, parameter_declaration_type))(s)
}

pub fn parameter_declaration_param(s: Span) -> IResult<Span, ParameterDeclaration> {
    let (s, _) = symbol("parameter")(s)?;
    let (s, x) = data_type_or_implicit(s)?;
    let (s, y) = list_of_param_assignments(s)?;
    Ok((
        s,
        ParameterDeclaration::Param(ParameterDeclarationParam { nodes: (x, y) }),
    ))
}

pub fn parameter_declaration_type(s: Span) -> IResult<Span, ParameterDeclaration> {
    let (s, _) = symbol("parameter")(s)?;
    let (s, _) = symbol("type")(s)?;
    let (s, x) = list_of_type_assignments(s)?;
    Ok((
        s,
        ParameterDeclaration::Type(ParameterDeclarationType { nodes: (x,) }),
    ))
}

pub fn specparam_declaration(s: Span) -> IResult<Span, SpecparamDeclaration> {
    let (s, _) = symbol("specparam")(s)?;
    let (s, x) = opt(packed_dimension)(s)?;
    let (s, y) = list_of_specparam_assignments(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, SpecparamDeclaration { nodes: (x, y) }))
}
