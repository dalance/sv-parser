use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct ConstraintDeclaration {
    pub nodes: (
        Option<Static>,
        Keyword,
        ConstraintIdentifier,
        ConstraintBlock,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct Static {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, Node)]
pub struct ConstraintBlock {
    pub nodes: (Brace<Vec<ConstraintBlockItem>>,),
}

#[derive(Clone, Debug, Node)]
pub enum ConstraintBlockItem {
    Solve(Box<ConstraintBlockItemSolve>),
    ConstraintExpression(Box<ConstraintExpression>),
}

#[derive(Clone, Debug, Node)]
pub struct ConstraintBlockItemSolve {
    pub nodes: (Keyword, SolveBeforeList, Keyword, SolveBeforeList, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct SolveBeforeList {
    pub nodes: (List<Symbol, ConstraintPrimary>,),
}

#[derive(Clone, Debug, Node)]
pub struct ConstraintPrimary {
    pub nodes: (
        Option<ImplicitClassHandleOrClassScope>,
        HierarchicalIdentifier,
        Select,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum ConstraintExpression {
    Expression(Box<ConstraintExpressionExpression>),
    UniquenessConstraint(Box<(UniquenessConstraint, Symbol)>),
    Arrow(Box<ConstraintExpressionArrow>),
    If(Box<ConstraintExpressionIf>),
    Foreach(Box<ConstraintExpressionForeach>),
    Disable(Box<ConstraintExpressionDisable>),
}

#[derive(Clone, Debug, Node)]
pub struct ConstraintExpressionExpression {
    pub nodes: (Option<Soft>, ExpressionOrDist, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct Soft {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, Node)]
pub struct ConstraintExpressionArrow {
    pub nodes: (Expression, Symbol, ConstraintSet),
}

#[derive(Clone, Debug, Node)]
pub struct ConstraintExpressionIf {
    pub nodes: (
        Keyword,
        Paren<Expression>,
        ConstraintSet,
        Option<(Keyword, ConstraintSet)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ConstraintExpressionForeach {
    pub nodes: (
        Keyword,
        Paren<(PsOrHierarchicalArrayIdentifier, Bracket<LoopVariables>)>,
        ConstraintSet,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ConstraintExpressionDisable {
    pub nodes: (Keyword, Keyword, ConstraintPrimary, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct UniquenessConstraint {
    pub nodes: (Keyword, Brace<OpenRangeList>),
}

#[derive(Clone, Debug, Node)]
pub enum ConstraintSet {
    ConstraintExpression(Box<ConstraintExpression>),
    Brace(Box<ConstraintSetBrace>),
}

#[derive(Clone, Debug, Node)]
pub struct ConstraintSetBrace {
    pub nodes: (Brace<Vec<ConstraintExpression>>,),
}

#[derive(Clone, Debug, Node)]
pub struct DistList {
    pub nodes: (List<Symbol, DistItem>,),
}

#[derive(Clone, Debug, Node)]
pub struct DistItem {
    pub nodes: (ValueRange, Option<DistWeight>),
}

#[derive(Clone, Debug, Node)]
pub enum DistWeight {
    Equal(Box<DistWeightEqual>),
    Divide(Box<DistWeightDivide>),
}

#[derive(Clone, Debug, Node)]
pub struct DistWeightEqual {
    pub nodes: (Symbol, Expression),
}

#[derive(Clone, Debug, Node)]
pub struct DistWeightDivide {
    pub nodes: (Symbol, Expression),
}

#[derive(Clone, Debug, Node)]
pub struct ConstraintPrototype {
    pub nodes: (
        Option<ConstraintPrototypeQualifier>,
        Option<Static>,
        Keyword,
        ConstraintIdentifier,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum ConstraintPrototypeQualifier {
    Extern(Box<Keyword>),
    Pure(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub struct ExternConstraintDeclaration {
    pub nodes: (
        Option<Static>,
        Keyword,
        ClassScope,
        ConstraintIdentifier,
        ConstraintBlock,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct IdentifierList {
    pub nodes: (List<Symbol, Identifier>,),
}
