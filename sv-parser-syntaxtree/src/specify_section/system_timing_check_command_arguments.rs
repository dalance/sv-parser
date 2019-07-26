use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct TimecheckCondition {
    pub nodes: (MintypmaxExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct ControlledReferenceEvent {
    pub nodes: (ControlledTimingCheckEvent,),
}

#[derive(Clone, Debug, Node)]
pub struct DataEvent {
    pub nodes: (TimingCheckEvent,),
}

#[derive(Clone, Debug, Node)]
pub enum DelayedData {
    TerminalIdentifier(Box<TerminalIdentifier>),
    WithMintypmax(Box<DelayedDataWithMintypmax>),
}

#[derive(Clone, Debug, Node)]
pub struct DelayedDataWithMintypmax {
    pub nodes: (TerminalIdentifier, Bracket<ConstantMintypmaxExpression>),
}

#[derive(Clone, Debug, Node)]
pub enum DelayedReference {
    TerminalIdentifier(Box<TerminalIdentifier>),
    WithMintypmax(Box<DelayedReferenceWithMintypmax>),
}

#[derive(Clone, Debug, Node)]
pub struct DelayedReferenceWithMintypmax {
    pub nodes: (TerminalIdentifier, Bracket<ConstantMintypmaxExpression>),
}

#[derive(Clone, Debug, Node)]
pub struct EndEdgeOffset {
    pub nodes: (MintypmaxExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct EventBasedFlag {
    pub nodes: (ConstantExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct Notifier {
    pub nodes: (VariableIdentifier,),
}

#[derive(Clone, Debug, Node)]
pub struct ReferenceEvent {
    pub nodes: (TimingCheckEvent,),
}

#[derive(Clone, Debug, Node)]
pub struct RemainActiveFlag {
    pub nodes: (ConstantMintypmaxExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct TimestampCondition {
    pub nodes: (MintypmaxExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct StartEdgeOffset {
    pub nodes: (MintypmaxExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct Threshold {
    pub nodes: (ConstantExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct TimingCheckLimit {
    pub nodes: (Expression,),
}
