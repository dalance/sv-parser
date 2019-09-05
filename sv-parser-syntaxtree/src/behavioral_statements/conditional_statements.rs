use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ConditionalStatement {
    pub nodes: (
        Option<UniquePriority>,
        Keyword,
        Paren<CondPredicate>,
        StatementOrNull,
        Vec<(Keyword, Keyword, Paren<CondPredicate>, StatementOrNull)>,
        Option<(Keyword, StatementOrNull)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum UniquePriority {
    Unique(Box<Keyword>),
    Unique0(Box<Keyword>),
    Priority(Box<Keyword>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CondPredicate {
    pub nodes: (List<Symbol, ExpressionOrCondPattern>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ExpressionOrCondPattern {
    Expression(Box<Expression>),
    CondPattern(Box<CondPattern>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CondPattern {
    pub nodes: (Expression, Keyword, Pattern),
}
