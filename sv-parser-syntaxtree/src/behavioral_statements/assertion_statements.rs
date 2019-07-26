use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum AssertionItem {
    Concurrent(Box<ConcurrentAssertionItem>),
    Immediate(Box<DeferredImmediateAssetionItem>),
}

#[derive(Clone, Debug, Node)]
pub struct DeferredImmediateAssetionItem {
    pub nodes: (
        Option<(BlockIdentifier, Symbol)>,
        DeferredImmediateAssertionStatement,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum ProceduralAssertionStatement {
    Concurrent(Box<ConcurrentAssertionStatement>),
    Immediate(Box<ImmediateAssetionStatement>),
    Checker(Box<CheckerInstantiation>),
}

#[derive(Clone, Debug, Node)]
pub enum ImmediateAssetionStatement {
    Simple(Box<SimpleImmediateAssertionStatement>),
    Deferred(Box<DeferredImmediateAssertionStatement>),
}

#[derive(Clone, Debug, Node)]
pub enum SimpleImmediateAssertionStatement {
    Assert(Box<SimpleImmediateAssertStatement>),
    Assume(Box<SimpleImmediateAssumeStatement>),
    Cover(Box<SimpleImmediateCoverStatement>),
}

#[derive(Clone, Debug, Node)]
pub struct SimpleImmediateAssertStatement {
    pub nodes: (Keyword, Paren<Expression>, ActionBlock),
}

#[derive(Clone, Debug, Node)]
pub struct SimpleImmediateAssumeStatement {
    pub nodes: (Keyword, Paren<Expression>, ActionBlock),
}

#[derive(Clone, Debug, Node)]
pub struct SimpleImmediateCoverStatement {
    pub nodes: (Keyword, Paren<Expression>, StatementOrNull),
}

#[derive(Clone, Debug, Node)]
pub enum DeferredImmediateAssertionStatement {
    Assert(Box<DeferredImmediateAssertStatement>),
    Assume(Box<DeferredImmediateAssumeStatement>),
    Cover(Box<DeferredImmediateCoverStatement>),
}

#[derive(Clone, Debug, Node)]
pub struct DeferredImmediateAssertStatement {
    pub nodes: (Keyword, AssertTiming, Paren<Expression>, ActionBlock),
}

#[derive(Clone, Debug, Node)]
pub struct DeferredImmediateAssumeStatement {
    pub nodes: (Keyword, AssertTiming, Paren<Expression>, ActionBlock),
}

#[derive(Clone, Debug, Node)]
pub struct DeferredImmediateCoverStatement {
    pub nodes: (Keyword, AssertTiming, Paren<Expression>, StatementOrNull),
}

#[derive(Clone, Debug, Node)]
pub enum AssertTiming {
    Zero(Box<Symbol>),
    Final(Box<Keyword>),
}
