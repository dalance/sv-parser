use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum CaseStatement {
    Normal(Box<CaseStatementNormal>),
    Matches(Box<CaseStatementMatches>),
    Inside(Box<CaseStatementInside>),
}

#[derive(Clone, Debug, Node)]
pub struct CaseStatementNormal {
    pub nodes: (
        Option<UniquePriority>,
        CaseKeyword,
        Paren<CaseExpression>,
        CaseItem,
        Vec<CaseItem>,
        Keyword,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct CaseStatementMatches {
    pub nodes: (
        Option<UniquePriority>,
        CaseKeyword,
        Paren<CaseExpression>,
        Keyword,
        CasePatternItem,
        Vec<CasePatternItem>,
        Keyword,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct CaseStatementInside {
    pub nodes: (
        Option<UniquePriority>,
        Keyword,
        Paren<CaseExpression>,
        Keyword,
        CaseInsideItem,
        Vec<CaseInsideItem>,
        Keyword,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum CaseKeyword {
    Case(Box<Keyword>),
    Casez(Box<Keyword>),
    Casex(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub struct CaseExpression {
    pub nodes: (Expression,),
}

#[derive(Clone, Debug, Node)]
pub enum CaseItem {
    NonDefault(Box<CaseItemNondefault>),
    Default(Box<CaseItemDefault>),
}

#[derive(Clone, Debug, Node)]
pub struct CaseItemNondefault {
    pub nodes: (List<Symbol, CaseItemExpression>, Symbol, StatementOrNull),
}

#[derive(Clone, Debug, Node)]
pub struct CaseItemDefault {
    pub nodes: (Keyword, Option<Symbol>, StatementOrNull),
}

#[derive(Clone, Debug, Node)]
pub enum CasePatternItem {
    NonDefault(Box<CasePatternItemNondefault>),
    Default(Box<CaseItemDefault>),
}

#[derive(Clone, Debug, Node)]
pub struct CasePatternItemNondefault {
    pub nodes: (
        Pattern,
        Option<(Symbol, Expression)>,
        Symbol,
        StatementOrNull,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum CaseInsideItem {
    NonDefault(Box<CaseInsideItemNondefault>),
    Default(Box<CaseItemDefault>),
}

#[derive(Clone, Debug, Node)]
pub struct CaseInsideItemNondefault {
    pub nodes: (OpenRangeList, Symbol, StatementOrNull),
}

#[derive(Clone, Debug, Node)]
pub struct CaseItemExpression {
    pub nodes: (Expression,),
}

#[derive(Clone, Debug, Node)]
pub struct RandcaseStatement {
    pub nodes: (Keyword, RandcaseItem, Vec<RandcaseItem>, Keyword),
}

#[derive(Clone, Debug, Node)]
pub struct RandcaseItem {
    pub nodes: (Expression, Symbol, StatementOrNull),
}

#[derive(Clone, Debug, Node)]
pub struct OpenRangeList {
    pub nodes: (List<Symbol, OpenValueRange>,),
}

#[derive(Clone, Debug, Node)]
pub struct OpenValueRange {
    pub nodes: (ValueRange,),
}
