use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum UdpBody {
    CombinationalBody(Box<CombinationalBody>),
    SequentialBody(Box<SequentialBody>),
}

#[derive(Clone, Debug, Node)]
pub struct CombinationalBody {
    pub nodes: (
        Keyword,
        CombinationalEntry,
        Vec<CombinationalEntry>,
        Keyword,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct CombinationalEntry {
    pub nodes: (LevelInputList, Symbol, OutputSymbol, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct SequentialBody {
    pub nodes: (
        Option<UdpInitialStatement>,
        Keyword,
        SequentialEntry,
        Vec<SequentialEntry>,
        Keyword,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct UdpInitialStatement {
    pub nodes: (Keyword, OutputPortIdentifier, Symbol, InitVal, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct InitVal {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, Node)]
pub struct SequentialEntry {
    pub nodes: (
        SeqInputList,
        Symbol,
        CurrentState,
        Symbol,
        NextState,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum SeqInputList {
    LevelInputList(Box<LevelInputList>),
    EdgeInputList(Box<EdgeInputList>),
}

#[derive(Clone, Debug, Node)]
pub struct LevelInputList {
    pub nodes: (LevelSymbol, Vec<LevelSymbol>),
}

#[derive(Clone, Debug, Node)]
pub struct EdgeInputList {
    pub nodes: (Vec<LevelSymbol>, EdgeIndicator, Vec<LevelSymbol>),
}

#[derive(Clone, Debug, Node)]
pub enum EdgeIndicator {
    Paren(Box<EdgeIndicatorParen>),
    EdgeSymbol(Box<EdgeSymbol>),
}

#[derive(Clone, Debug, Node)]
pub struct EdgeIndicatorParen {
    pub nodes: (Paren<(LevelSymbol, LevelSymbol)>,),
}

#[derive(Clone, Debug, Node)]
pub struct CurrentState {
    pub nodes: (LevelSymbol,),
}

#[derive(Clone, Debug, Node)]
pub enum NextState {
    OutputSymbol(Box<OutputSymbol>),
    Minus(Box<Symbol>),
}

#[derive(Clone, Debug, Node)]
pub struct OutputSymbol {
    pub nodes: (Symbol,),
}

#[derive(Clone, Debug, Node)]
pub struct LevelSymbol {
    pub nodes: (Symbol,),
}

#[derive(Clone, Debug, Node)]
pub struct EdgeSymbol {
    pub nodes: (Symbol,),
}
