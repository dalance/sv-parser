use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PreprocessorText {
    pub nodes: (Vec<SourceDescription>,),
}

