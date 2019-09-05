use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ProgramInstantiation {
    pub nodes: (
        ProgramIdentifier,
        Option<ParameterValueAssignment>,
        List<Symbol, HierarchicalInstance>,
        Symbol,
    ),
}
