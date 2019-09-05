use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub struct UnaryOperator {
    pub nodes: (Symbol,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct BinaryOperator {
    pub nodes: (Symbol,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct IncOrDecOperator {
    pub nodes: (Symbol,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct UnaryModulePathOperator {
    pub nodes: (Symbol,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct BinaryModulePathOperator {
    pub nodes: (Symbol,),
}
