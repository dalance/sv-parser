use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub struct AttributeInstance {
    pub nodes: (Symbol, List<Symbol, AttrSpec>, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct AttrSpec {
    pub nodes: (Identifier, Option<(Symbol, ConstantExpression)>),
}
