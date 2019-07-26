use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct UnaryOperator {
    pub nodes: (Symbol,),
}

#[derive(Clone, Debug, Node)]
pub struct BinaryOperator {
    pub nodes: (Symbol,),
}

#[derive(Clone, Debug, Node)]
pub struct IncOrDecOperator {
    pub nodes: (Symbol,),
}

#[derive(Clone, Debug, Node)]
pub struct UnaryModulePathOperator {
    pub nodes: (Symbol,),
}

#[derive(Clone, Debug, Node)]
pub struct BinaryModulePathOperator {
    pub nodes: (Symbol,),
}
