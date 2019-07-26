use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum ClockingDeclaration {
    Local(Box<ClockingDeclarationLocal>),
    Global(Box<ClockingDeclarationGlobal>),
}

#[derive(Clone, Debug, Node)]
pub struct ClockingDeclarationLocal {
    pub nodes: (
        Option<Default>,
        Keyword,
        Option<ClockingIdentifier>,
        ClockingEvent,
        Symbol,
        Vec<ClockingItem>,
        Keyword,
        Option<(Symbol, ClockingIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct Default {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, Node)]
pub struct ClockingDeclarationGlobal {
    pub nodes: (
        Keyword,
        Keyword,
        Option<ClockingIdentifier>,
        ClockingEvent,
        Symbol,
        Keyword,
        Option<(Symbol, ClockingIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum ClockingEvent {
    Identifier(Box<ClockingEventIdentifier>),
    Expression(Box<ClockingEventExpression>),
}

#[derive(Clone, Debug, Node)]
pub struct ClockingEventIdentifier {
    pub nodes: (Symbol, Identifier),
}

#[derive(Clone, Debug, Node)]
pub struct ClockingEventExpression {
    pub nodes: (Symbol, Paren<EventExpression>),
}

#[derive(Clone, Debug, Node)]
pub enum ClockingItem {
    Default(Box<ClockingItemDefault>),
    Direction(Box<ClockingItemDirection>),
    Assertion(Box<ClockingItemAssertion>),
}

#[derive(Clone, Debug, Node)]
pub struct ClockingItemDefault {
    pub nodes: (Keyword, DefaultSkew, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct ClockingItemDirection {
    pub nodes: (ClockingDirection, ListOfClockingDeclAssign, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct ClockingItemAssertion {
    pub nodes: (Vec<AttributeInstance>, AssertionItemDeclaration),
}

#[derive(Clone, Debug, Node)]
pub enum DefaultSkew {
    Input(Box<DefaultSkewInput>),
    Output(Box<DefaultSkewOutput>),
    InputOutput(Box<DefaultSkewInputOutput>),
}

#[derive(Clone, Debug, Node)]
pub struct DefaultSkewInput {
    pub nodes: (Keyword, ClockingSkew),
}

#[derive(Clone, Debug, Node)]
pub struct DefaultSkewOutput {
    pub nodes: (Keyword, ClockingSkew),
}

#[derive(Clone, Debug, Node)]
pub struct DefaultSkewInputOutput {
    pub nodes: (Keyword, ClockingSkew, Keyword, ClockingSkew),
}

#[derive(Clone, Debug, Node)]
pub enum ClockingDirection {
    Input(Box<ClockingDirectionInput>),
    Output(Box<ClockingDirectionOutput>),
    InputOutput(Box<ClockingDirectionInputOutput>),
    Inout(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub struct ClockingDirectionInput {
    pub nodes: (Keyword, Option<ClockingSkew>),
}

#[derive(Clone, Debug, Node)]
pub struct ClockingDirectionOutput {
    pub nodes: (Keyword, Option<ClockingSkew>),
}

#[derive(Clone, Debug, Node)]
pub struct ClockingDirectionInputOutput {
    pub nodes: (Keyword, Option<ClockingSkew>, Keyword, Option<ClockingSkew>),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfClockingDeclAssign {
    pub nodes: (List<Symbol, ClockingDeclAssign>,),
}

#[derive(Clone, Debug, Node)]
pub struct ClockingDeclAssign {
    pub nodes: (SignalIdentifier, Option<(Symbol, Expression)>),
}

#[derive(Clone, Debug, Node)]
pub enum ClockingSkew {
    Edge(Box<ClockingSkewEdge>),
    DelayControl(Box<DelayControl>),
}

#[derive(Clone, Debug, Node)]
pub struct ClockingSkewEdge {
    pub nodes: (EdgeIdentifier, Option<DelayControl>),
}

#[derive(Clone, Debug, Node)]
pub struct ClockingDrive {
    pub nodes: (ClockvarExpression, Symbol, Option<CycleDelay>, Expression),
}

#[derive(Clone, Debug, Node)]
pub enum CycleDelay {
    Integral(Box<CycleDelayIntegral>),
    Identifier(Box<CycleDelayIdentifier>),
    Expression(Box<CycleDelayExpression>),
}

#[derive(Clone, Debug, Node)]
pub struct CycleDelayIntegral {
    pub nodes: (Symbol, IntegralNumber),
}

#[derive(Clone, Debug, Node)]
pub struct CycleDelayIdentifier {
    pub nodes: (Symbol, Identifier),
}

#[derive(Clone, Debug, Node)]
pub struct CycleDelayExpression {
    pub nodes: (Symbol, Paren<Expression>),
}

#[derive(Clone, Debug, Node)]
pub struct Clockvar {
    pub nodes: (HierarchicalIdentifier,),
}

#[derive(Clone, Debug, Node)]
pub struct ClockvarExpression {
    pub nodes: (Clockvar, Select),
}
