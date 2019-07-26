use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct CmosSwitchtype {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, Node)]
pub struct EnableGatetype {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, Node)]
pub struct MosSwitchtype {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, Node)]
pub struct NInputGatetype {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, Node)]
pub struct NOutputGatetype {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, Node)]
pub struct PassEnSwitchtype {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, Node)]
pub struct PassSwitchtype {
    pub nodes: (Keyword,),
}
