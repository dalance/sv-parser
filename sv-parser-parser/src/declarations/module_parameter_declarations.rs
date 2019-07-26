use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn local_parameter_declaration(s: Span) -> IResult<Span, LocalParameterDeclaration> {
    alt((
        local_parameter_declaration_param,
        local_parameter_declaration_type,
    ))(s)
}

#[parser(Ambiguous)]
#[tracable_parser]
pub(crate) fn local_parameter_declaration_param(
    s: Span,
) -> IResult<Span, LocalParameterDeclaration> {
    let (s, a) = keyword("localparam")(s)?;
    let (s, b) = ambiguous_opt(data_type_or_implicit)(s)?;
    let (s, c) = list_of_param_assignments(s)?;
    Ok((
        s,
        LocalParameterDeclaration::Param(Box::new(LocalParameterDeclarationParam {
            nodes: (a, b, c),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn local_parameter_declaration_type(
    s: Span,
) -> IResult<Span, LocalParameterDeclaration> {
    let (s, a) = keyword("localparam")(s)?;
    let (s, b) = keyword("type")(s)?;
    let (s, c) = list_of_type_assignments(s)?;
    Ok((
        s,
        LocalParameterDeclaration::Type(Box::new(LocalParameterDeclarationType {
            nodes: (a, b, c),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn parameter_declaration(s: Span) -> IResult<Span, ParameterDeclaration> {
    alt((parameter_declaration_param, parameter_declaration_type))(s)
}

#[parser(Ambiguous)]
#[tracable_parser]
pub(crate) fn parameter_declaration_param(s: Span) -> IResult<Span, ParameterDeclaration> {
    let (s, a) = keyword("parameter")(s)?;
    let (s, b) = ambiguous_opt(data_type_or_implicit)(s)?;
    let (s, c) = list_of_param_assignments(s)?;
    Ok((
        s,
        ParameterDeclaration::Param(Box::new(ParameterDeclarationParam { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn parameter_declaration_type(s: Span) -> IResult<Span, ParameterDeclaration> {
    let (s, a) = keyword("parameter")(s)?;
    let (s, b) = keyword("type")(s)?;
    let (s, c) = list_of_type_assignments(s)?;
    Ok((
        s,
        ParameterDeclaration::Type(Box::new(ParameterDeclarationType { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn specparam_declaration(s: Span) -> IResult<Span, SpecparamDeclaration> {
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
