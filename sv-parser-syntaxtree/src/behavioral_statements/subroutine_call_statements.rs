use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum SubroutineCallStatement {
    SubroutineCall(Box<(SubroutineCall, Symbol)>),
    Function(Box<SubroutineCallStatementFunction>),
}

#[derive(Clone, Debug, Node)]
pub struct SubroutineCallStatementFunction {
    pub nodes: (Keyword, Symbol, Paren<FunctionSubroutineCall>, Symbol),
}
