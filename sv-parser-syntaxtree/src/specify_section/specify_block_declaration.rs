use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SpecifyBlock {
    pub nodes: (Keyword, Vec<SpecifyItem>, Keyword),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum SpecifyItem {
    SpecparamDeclaration(Box<SpecparamDeclaration>),
    PulsestyleDeclaration(Box<PulsestyleDeclaration>),
    ShowcancelledDeclaration(Box<ShowcancelledDeclaration>),
    PathDeclaration(Box<PathDeclaration>),
    SystemTimingCheck(Box<SystemTimingCheck>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PulsestyleDeclaration {
    pub nodes: (Keyword, ListOfPathOutputs, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ShowcancelledDeclaration {
    pub nodes: (Keyword, ListOfPathOutputs, Symbol),
}
