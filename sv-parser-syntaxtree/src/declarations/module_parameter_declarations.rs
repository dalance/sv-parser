use crate::*;

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
