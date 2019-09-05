use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub enum SubroutineCallStatement {
    SubroutineCall(Box<(SubroutineCall, Symbol)>),
    Function(Box<SubroutineCallStatementFunction>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SubroutineCallStatementFunction {
    pub nodes: (Keyword, Symbol, Paren<FunctionSubroutineCall>, Symbol),
}
