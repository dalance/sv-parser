use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct UdpInstantiation {
    pub nodes: (
        UdpIdentifier,
        Option<DriveStrength>,
        Option<Delay2>,
        List<Symbol, UdpInstance>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct UdpInstance {
    pub nodes: (
        Option<NameOfInstance>,
        Paren<(
            OutputTerminal,
            Symbol,
            InputTerminal,
            Vec<(Symbol, InputTerminal)>,
        )>,
    ),
}
