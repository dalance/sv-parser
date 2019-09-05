use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub struct EnableTerminal {
    pub nodes: (Expression,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct InoutTerminal {
    pub nodes: (NetLvalue,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct InputTerminal {
    pub nodes: (Expression,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct NcontrolTerminal {
    pub nodes: (Expression,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct OutputTerminal {
    pub nodes: (NetLvalue,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PcontrolTerminal {
    pub nodes: (Expression,),
}
