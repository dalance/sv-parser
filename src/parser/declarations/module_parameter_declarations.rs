use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum LocalParameterDeclaration {
    Param(Box<LocalParameterDeclarationParam>),
    Type(Box<LocalParameterDeclarationType>),
}

#[derive(Clone, Debug, Node)]
pub struct LocalParameterDeclarationParam {
    pub nodes: (Keyword, Option<DataTypeOrImplicit>, ListOfParamAssignments),
}

#[derive(Clone, Debug, Node)]
pub struct LocalParameterDeclarationType {
    pub nodes: (Keyword, Keyword, ListOfTypeAssignments),
}

#[derive(Clone, Debug, Node)]
pub enum ParameterDeclaration {
    Param(Box<ParameterDeclarationParam>),
    Type(Box<ParameterDeclarationType>),
}

#[derive(Clone, Debug, Node)]
pub struct ParameterDeclarationParam {
    pub nodes: (Keyword, Option<DataTypeOrImplicit>, ListOfParamAssignments),
}

#[derive(Clone, Debug, Node)]
pub struct ParameterDeclarationType {
    pub nodes: (Keyword, Keyword, ListOfTypeAssignments),
}

#[derive(Clone, Debug, Node)]
pub struct SpecparamDeclaration {
    pub nodes: (
        Keyword,
        Option<PackedDimension>,
        ListOfSpecparamAssignments,
        Symbol,
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
        LocalParameterDeclaration::Param(Box::new(LocalParameterDeclarationParam {
            nodes: (a, b, c),
        })),
    ))
}

#[parser]
pub fn local_parameter_declaration_type(s: Span) -> IResult<Span, LocalParameterDeclaration> {
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
        ParameterDeclaration::Param(Box::new(ParameterDeclarationParam { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn parameter_declaration_type(s: Span) -> IResult<Span, ParameterDeclaration> {
    let (s, a) = keyword("parameter")(s)?;
    let (s, b) = keyword("type")(s)?;
    let (s, c) = list_of_type_assignments(s)?;
    Ok((
        s,
        ParameterDeclaration::Type(Box::new(ParameterDeclarationType { nodes: (a, b, c) })),
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

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_local_parameter_declaration() {
        parser_test!(
            local_parameter_declaration,
            "localparam byte colon1 = \":\" ",
            Ok((_, LocalParameterDeclaration::Param(_)))
        );
    }

    #[test]
    fn test_parameter_declaration() {
        parser_test!(
            parameter_declaration,
            "parameter logic flag = 1 ",
            Ok((_, ParameterDeclaration::Param(_)))
        );
        parser_test!(
            parameter_declaration,
            "parameter e = 25, f = 9 ",
            Ok((_, ParameterDeclaration::Param(_)))
        );
        parser_test!(
            parameter_declaration,
            "parameter byte_size = 8, byte_mask = byte_size - 1",
            Ok((_, ParameterDeclaration::Param(_)))
        );
        parser_test!(
            parameter_declaration,
            "parameter signed [3:0] mux_selector = 0",
            Ok((_, ParameterDeclaration::Param(_)))
        );
        parser_test!(
            parameter_declaration,
            "parameter real r1 = 3.5e17",
            Ok((_, ParameterDeclaration::Param(_)))
        );
        parser_test!(
            parameter_declaration,
            "parameter logic [31:0] P1 [3:0] = '{ 1, 2, 3, 4 } ",
            Ok((_, ParameterDeclaration::Param(_)))
        );
        parser_test!(
            parameter_declaration,
            "parameter r2 = $ ",
            Ok((_, ParameterDeclaration::Param(_)))
        );
        parser_test!(
            parameter_declaration,
            "parameter type p2 = shortint ",
            Ok((_, ParameterDeclaration::Type(_)))
        );
    }

    #[test]
    fn test_specparam_declaration() {
        parser_test!(specparam_declaration, "specparam delay = 10 ; ", Ok((_, _)));
        parser_test!(
            specparam_declaration,
            "specparam tRise_clk_q = 150, tFall_clk_q = 200;",
            Ok((_, _))
        );
    }
}
