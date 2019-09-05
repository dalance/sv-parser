use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ContinuousAssign {
    Net(Box<ContinuousAssignNet>),
    Variable(Box<ContinuousAssignVariable>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ContinuousAssignNet {
    pub nodes: (
        Keyword,
        Option<DriveStrength>,
        Option<Delay3>,
        ListOfNetAssignments,
        Symbol,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ContinuousAssignVariable {
    pub nodes: (
        Keyword,
        Option<DelayControl>,
        ListOfVariableAssignments,
        Symbol,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ListOfNetAssignments {
    pub nodes: (List<Symbol, NetAssignment>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ListOfVariableAssignments {
    pub nodes: (List<Symbol, VariableAssignment>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct NetAlias {
    pub nodes: (Keyword, NetLvalue, Symbol, List<Symbol, NetLvalue>, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct NetAssignment {
    pub nodes: (NetLvalue, Symbol, Expression),
}
