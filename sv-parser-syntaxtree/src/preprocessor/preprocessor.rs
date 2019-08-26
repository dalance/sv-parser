use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct PreprocessorText {
    pub nodes: (Vec<SourceDescription>,),
}

