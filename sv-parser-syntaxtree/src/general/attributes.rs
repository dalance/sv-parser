use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct AttributeInstance {
    pub nodes: (Symbol, List<Symbol, AttrSpec>, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct AttrSpec {
    pub nodes: (Identifier, Option<(Symbol, ConstantExpression)>),
}
