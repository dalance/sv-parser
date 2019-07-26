use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum PathDeclaration {
    SimplePathDeclaration(Box<(SimplePathDeclaration, Symbol)>),
    EdgeSensitivePathDeclaration(Box<(EdgeSensitivePathDeclaration, Symbol)>),
    StateDependentPathDeclaration(Box<(StateDependentPathDeclaration, Symbol)>),
}

#[derive(Clone, Debug, Node)]
pub enum SimplePathDeclaration {
    Parallel(Box<SimplePathDeclarationParallel>),
    Full(Box<SimplePathDeclarationFull>),
}

#[derive(Clone, Debug, Node)]
pub struct SimplePathDeclarationParallel {
    pub nodes: (ParallelPathDescription, Symbol, PathDelayValue),
}

#[derive(Clone, Debug, Node)]
pub struct SimplePathDeclarationFull {
    pub nodes: (FullPathDescription, Symbol, PathDelayValue),
}

#[derive(Clone, Debug, Node)]
pub struct ParallelPathDescription {
    pub nodes: (
        Paren<(
            SpecifyInputTerminalDescriptor,
            Option<PolarityOperator>,
            Symbol,
            SpecifyOutputTerminalDescriptor,
        )>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct FullPathDescription {
    pub nodes: (
        Paren<(
            ListOfPathInputs,
            Option<PolarityOperator>,
            Symbol,
            ListOfPathOutputs,
        )>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfPathInputs {
    pub nodes: (List<Symbol, SpecifyInputTerminalDescriptor>,),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfPathOutputs {
    pub nodes: (List<Symbol, SpecifyOutputTerminalDescriptor>,),
}
