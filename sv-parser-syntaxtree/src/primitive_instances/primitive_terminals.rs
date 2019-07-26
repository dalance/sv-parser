use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct EnableTerminal {
    pub nodes: (Expression,),
}

#[derive(Clone, Debug, Node)]
pub struct InoutTerminal {
    pub nodes: (NetLvalue,),
}

#[derive(Clone, Debug, Node)]
pub struct InputTerminal {
    pub nodes: (Expression,),
}

#[derive(Clone, Debug, Node)]
pub struct NcontrolTerminal {
    pub nodes: (Expression,),
}

#[derive(Clone, Debug, Node)]
pub struct OutputTerminal {
    pub nodes: (NetLvalue,),
}

#[derive(Clone, Debug, Node)]
pub struct PcontrolTerminal {
    pub nodes: (Expression,),
}
