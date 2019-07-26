use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct GenerateRegion {
    pub nodes: (Keyword, Vec<GenerateItem>, Keyword),
}

#[derive(Clone, Debug, Node)]
pub struct LoopGenerateConstruct {
    pub nodes: (
        Keyword,
        Paren<(
            GenvarInitialization,
            Symbol,
            GenvarExpression,
            Symbol,
            GenvarIteration,
        )>,
        GenerateBlock,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct GenvarInitialization {
    pub nodes: (Option<Genvar>, GenvarIdentifier, Symbol, ConstantExpression),
}

#[derive(Clone, Debug, Node)]
pub struct Genvar {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, Node)]
pub enum GenvarIteration {
    Assignment(Box<GenvarIterationAssignment>),
    Prefix(Box<GenvarIterationPrefix>),
    Suffix(Box<GenvarIterationSuffix>),
}

#[derive(Clone, Debug, Node)]
pub struct GenvarIterationAssignment {
    pub nodes: (GenvarIdentifier, AssignmentOperator, GenvarExpression),
}

#[derive(Clone, Debug, Node)]
pub struct GenvarIterationPrefix {
    pub nodes: (IncOrDecOperator, GenvarIdentifier),
}

#[derive(Clone, Debug, Node)]
pub struct GenvarIterationSuffix {
    pub nodes: (GenvarIdentifier, IncOrDecOperator),
}

#[derive(Clone, Debug, Node)]
pub enum ConditionalGenerateConstruct {
    If(Box<IfGenerateConstruct>),
    Case(Box<CaseGenerateConstruct>),
}

#[derive(Clone, Debug, Node)]
pub struct IfGenerateConstruct {
    pub nodes: (
        Keyword,
        Paren<ConstantExpression>,
        GenerateBlock,
        Option<(Keyword, GenerateBlock)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct CaseGenerateConstruct {
    pub nodes: (
        Keyword,
        Paren<ConstantExpression>,
        Vec<CaseGenerateItem>,
        Keyword,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum CaseGenerateItem {
    Nondefault(Box<CaseGenerateItemNondefault>),
    Default(Box<CaseGenerateItemDefault>),
}

#[derive(Clone, Debug, Node)]
pub struct CaseGenerateItemNondefault {
    pub nodes: (List<Symbol, ConstantExpression>, Symbol, GenerateBlock),
}

#[derive(Clone, Debug, Node)]
pub struct CaseGenerateItemDefault {
    pub nodes: (Keyword, Option<Symbol>, GenerateBlock),
}

#[derive(Clone, Debug, Node)]
pub enum GenerateBlock {
    GenerateItem(Box<GenerateItem>),
    Multiple(Box<GenerateBlockMultiple>),
}

#[derive(Clone, Debug, Node)]
pub struct GenerateBlockMultiple {
    pub nodes: (
        Option<(GenerateBlockIdentifier, Symbol)>,
        Keyword,
        Option<(Symbol, GenerateBlockIdentifier)>,
        Vec<GenerateItem>,
        Keyword,
        Option<(Symbol, GenerateBlockIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum GenerateItem {
    ModuleOrGenerateItem(Box<ModuleOrGenerateItem>),
    InterfaceOrGenerateItem(Box<InterfaceOrGenerateItem>),
    CheckerOrGenerateItem(Box<CheckerOrGenerateItem>),
}
