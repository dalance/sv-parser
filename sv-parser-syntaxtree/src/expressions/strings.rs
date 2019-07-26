use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct StringLiteral {
    pub nodes: (Locate, Vec<WhiteSpace>),
}
