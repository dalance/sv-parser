use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum LocalParameterDeclaration<'a> {
    Param(LocalParameterDeclarationParam<'a>),
    Type(LocalParameterDeclarationType<'a>),
}

#[derive(Debug, Node)]
pub struct LocalParameterDeclarationParam<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<DataTypeOrImplicit<'a>>,
        ListOfParamAssignments<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct LocalParameterDeclarationType<'a> {
    pub nodes: (Symbol<'a>, Symbol<'a>, ListOfTypeAssignments<'a>),
}

#[derive(Debug, Node)]
pub enum ParameterDeclaration<'a> {
    Param(ParameterDeclarationParam<'a>),
    Type(ParameterDeclarationType<'a>),
}

#[derive(Debug, Node)]
pub struct ParameterDeclarationParam<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<DataTypeOrImplicit<'a>>,
        ListOfParamAssignments<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ParameterDeclarationType<'a> {
    pub nodes: (Symbol<'a>, Symbol<'a>, ListOfTypeAssignments<'a>),
}

#[derive(Debug, Node)]
pub struct SpecparamDeclaration<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<PackedDimension<'a>>,
        ListOfSpecparamAssignments<'a>,
        Symbol<'a>,
    ),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn local_parameter_declaration(s: Span) -> IResult<Span, LocalParameterDeclaration> {
    alt((
        local_parameter_declaration_param,
        local_parameter_declaration_type,
    ))(s)
}

#[parser(Ambiguous)]
pub fn local_parameter_declaration_param(s: Span) -> IResult<Span, LocalParameterDeclaration> {
    let (s, a) = keyword("localparam")(s)?;
    let (s, b) = ambiguous_opt(data_type_or_implicit)(s)?;
    let (s, c) = list_of_param_assignments(s)?;
    Ok((
        s,
        LocalParameterDeclaration::Param(LocalParameterDeclarationParam { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn local_parameter_declaration_type(s: Span) -> IResult<Span, LocalParameterDeclaration> {
    let (s, a) = keyword("localparam")(s)?;
    let (s, b) = keyword("type")(s)?;
    let (s, c) = list_of_type_assignments(s)?;
    Ok((
        s,
        LocalParameterDeclaration::Type(LocalParameterDeclarationType { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn parameter_declaration(s: Span) -> IResult<Span, ParameterDeclaration> {
    alt((parameter_declaration_param, parameter_declaration_type))(s)
}

#[parser(Ambiguous)]
pub fn parameter_declaration_param(s: Span) -> IResult<Span, ParameterDeclaration> {
    let (s, a) = keyword("parameter")(s)?;
    let (s, b) = ambiguous_opt(data_type_or_implicit)(s)?;
    let (s, c) = list_of_param_assignments(s)?;
    Ok((
        s,
        ParameterDeclaration::Param(ParameterDeclarationParam { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn parameter_declaration_type(s: Span) -> IResult<Span, ParameterDeclaration> {
    let (s, a) = keyword("parameter")(s)?;
    let (s, b) = keyword("type")(s)?;
    let (s, c) = list_of_type_assignments(s)?;
    Ok((
        s,
        ParameterDeclaration::Type(ParameterDeclarationType { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn specparam_declaration(s: Span) -> IResult<Span, SpecparamDeclaration> {
    let (s, a) = keyword("specparam")(s)?;
    let (s, b) = opt(packed_dimension)(s)?;
    let (s, c) = list_of_specparam_assignments(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        SpecparamDeclaration {
            nodes: (a, b, c, d),
        },
    ))
}
