use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub struct StringLiteral {
    pub nodes: (Locate, Vec<WhiteSpace>),
}
