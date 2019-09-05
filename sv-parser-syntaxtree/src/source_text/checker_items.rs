use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CheckerPortList {
    pub nodes: (List<Symbol, CheckerPortItem>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CheckerPortItem {
    pub nodes: (
        Vec<AttributeInstance>,
        Option<CheckerPortDirection>,
        PropertyFormalType,
        FormalPortIdentifier,
        Vec<VariableDimension>,
        Option<(Symbol, PropertyActualArg)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum CheckerPortDirection {
    Input(Box<Keyword>),
    Output(Box<Keyword>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum CheckerOrGenerateItem {
    CheckerOrGenerateItemDeclaration(Box<CheckerOrGenerateItemDeclaration>),
    InitialConstruct(Box<InitialConstruct>),
    AlwaysConstruct(Box<AlwaysConstruct>),
    FinalConstruct(Box<FinalConstruct>),
    AssertionItem(Box<AssertionItem>),
    ContinuousAssign(Box<ContinuousAssign>),
    CheckerGenerateItem(Box<CheckerGenerateItem>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum CheckerOrGenerateItemDeclaration {
    Data(Box<CheckerOrGenerateItemDeclarationData>),
    FunctionDeclaration(Box<FunctionDeclaration>),
    CheckerDeclaration(Box<CheckerDeclaration>),
    AssertionItemDeclaration(Box<AssertionItemDeclaration>),
    CovergroupDeclaration(Box<CovergroupDeclaration>),
    GenvarDeclaration(Box<GenvarDeclaration>),
    ClockingDeclaration(Box<ClockingDeclaration>),
    Clocking(Box<CheckerOrGenerateItemDeclarationClocking>),
    Disable(Box<CheckerOrGenerateItemDeclarationDisable>),
    Empty(Box<Symbol>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CheckerOrGenerateItemDeclarationData {
    pub nodes: (Option<Rand>, DataDeclaration),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct Rand {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CheckerOrGenerateItemDeclarationClocking {
    pub nodes: (Keyword, Keyword, ClockingIdentifier, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CheckerOrGenerateItemDeclarationDisable {
    pub nodes: (Keyword, Keyword, Keyword, ExpressionOrDist, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum CheckerGenerateItem {
    LoopGenerateConstruct(Box<LoopGenerateConstruct>),
    ConditionalGenerateConstruct(Box<ConditionalGenerateConstruct>),
    GenerateRegion(Box<GenerateRegion>),
    ElaborationSystemTask(Box<ElaborationSystemTask>),
}
