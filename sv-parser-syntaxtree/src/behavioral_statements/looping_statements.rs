use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum LoopStatement {
    Forever(Box<LoopStatementForever>),
    Repeat(Box<LoopStatementRepeat>),
    While(Box<LoopStatementWhile>),
    For(Box<LoopStatementFor>),
    DoWhile(Box<LoopStatementDoWhile>),
    Foreach(Box<LoopStatementForeach>),
}

#[derive(Clone, Debug, Node)]
pub struct LoopStatementForever {
    pub nodes: (Keyword, StatementOrNull),
}

#[derive(Clone, Debug, Node)]
pub struct LoopStatementRepeat {
    pub nodes: (Keyword, Paren<Expression>, StatementOrNull),
}

#[derive(Clone, Debug, Node)]
pub struct LoopStatementWhile {
    pub nodes: (Keyword, Paren<Expression>, StatementOrNull),
}

#[derive(Clone, Debug, Node)]
pub struct LoopStatementFor {
    pub nodes: (
        Keyword,
        Paren<(
            Option<ForInitialization>,
            Symbol,
            Option<Expression>,
            Symbol,
            Option<ForStep>,
        )>,
        StatementOrNull,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct LoopStatementDoWhile {
    pub nodes: (Keyword, StatementOrNull, Keyword, Paren<Expression>, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct LoopStatementForeach {
    pub nodes: (
        Keyword,
        Paren<(PsOrHierarchicalArrayIdentifier, Bracket<LoopVariables>)>,
        Statement,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum ForInitialization {
    ListOfVariableAssignments(Box<ListOfVariableAssignments>),
    Declaration(Box<ForInitializationDeclaration>),
}

#[derive(Clone, Debug, Node)]
pub struct ForInitializationDeclaration {
    pub nodes: (List<Symbol, ForVariableDeclaration>,),
}

#[derive(Clone, Debug, Node)]
pub struct ForVariableDeclaration {
    pub nodes: (
        Option<Var>,
        DataType,
        List<Symbol, (VariableIdentifier, Symbol, Expression)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct Var {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, Node)]
pub struct ForStep {
    pub nodes: (List<Symbol, ForStepAssignment>,),
}

#[derive(Clone, Debug, Node)]
pub enum ForStepAssignment {
    OperatorAssignment(Box<OperatorAssignment>),
    IncOrDecExpression(Box<IncOrDecExpression>),
    FunctionSubroutineCall(Box<FunctionSubroutineCall>),
}

#[derive(Clone, Debug, Node)]
pub struct LoopVariables {
    pub nodes: (List<Symbol, Option<IndexVariableIdentifier>>,),
}
