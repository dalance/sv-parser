use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct ConstraintDeclaration<'a> {
    pub nodes: (
        Option<Static<'a>>,
        ConstraintIdentifier<'a>,
        ConstraintBlock<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct Static<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub struct ConstraintBlock<'a> {
    pub nodes: (Vec<ConstraintBlockItem<'a>>,),
}

#[derive(Debug, Node)]
pub enum ConstraintBlockItem<'a> {
    Solve(ConstraintBlockItemSolve<'a>),
    ConstraintExpression(ConstraintExpression<'a>),
}

#[derive(Debug, Node)]
pub struct ConstraintBlockItemSolve<'a> {
    pub nodes: (SolveBeforeList<'a>, SolveBeforeList<'a>),
}

#[derive(Debug, Node)]
pub struct SolveBeforeList<'a> {
    pub nodes: (Vec<ConstraintPrimary<'a>>,),
}

#[derive(Debug, Node)]
pub struct ConstraintPrimary<'a> {
    pub nodes: (
        Option<ImplicitClassHandleOrClassScope<'a>>,
        HierarchicalIdentifier<'a>,
        Select<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum ConstraintExpression<'a> {
    Expression(ConstraintExpressionExpression<'a>),
    UniquenessConstraint(UniquenessConstraint<'a>),
    Arrow(ConstraintExpressionArrow<'a>),
    If(ConstraintExpressionIf<'a>),
    Foreach(ConstraintExpressionForeach<'a>),
    Disable(ConstraintExpressionDisable<'a>),
}

#[derive(Debug, Node)]
pub struct ConstraintExpressionExpression<'a> {
    pub nodes: (Option<Soft<'a>>, ExpressionOrDist<'a>),
}

#[derive(Debug, Node)]
pub struct Soft<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub struct ConstraintExpressionArrow<'a> {
    pub nodes: (Expression<'a>, ConstraintSet<'a>),
}

#[derive(Debug, Node)]
pub struct ConstraintExpressionIf<'a> {
    pub nodes: (Expression<'a>, ConstraintSet<'a>, Option<ConstraintSet<'a>>),
}

#[derive(Debug, Node)]
pub struct ConstraintExpressionForeach<'a> {
    pub nodes: (
        PsOrHierarchicalArrayIdentifier<'a>,
        LoopVariables<'a>,
        ConstraintSet<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ConstraintExpressionDisable<'a> {
    pub nodes: (ConstraintPrimary<'a>,),
}

#[derive(Debug, Node)]
pub struct UniquenessConstraint<'a> {
    pub nodes: (OpenRangeList<'a>,),
}

#[derive(Debug, Node)]
pub enum ConstraintSet<'a> {
    ConstraintExpression(Box<ConstraintExpression<'a>>),
    Bracket(ConstraintSetBracket<'a>),
}

#[derive(Debug, Node)]
pub struct ConstraintSetBracket<'a> {
    pub nodes: (Vec<ConstraintExpression<'a>>,),
}

#[derive(Debug, Node)]
pub struct DistList<'a> {
    pub nodes: (Vec<DistItem<'a>>,),
}

#[derive(Debug, Node)]
pub struct DistItem<'a> {
    pub nodes: (ValueRange<'a>, Option<DistWeight<'a>>),
}

#[derive(Debug, Node)]
pub enum DistWeight<'a> {
    Equal(DistWeightEqual<'a>),
    Divide(DistWeightDivide<'a>),
}

#[derive(Debug, Node)]
pub struct DistWeightEqual<'a> {
    pub nodes: (Expression<'a>,),
}

#[derive(Debug, Node)]
pub struct DistWeightDivide<'a> {
    pub nodes: (Expression<'a>,),
}

#[derive(Debug, Node)]
pub struct ConstraintPrototype<'a> {
    pub nodes: (
        Option<ConstraintPrototypeQualifier<'a>>,
        Option<Static<'a>>,
        ConstraintIdentifier<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum ConstraintPrototypeQualifier<'a> {
    Extern(Symbol<'a>),
    Pure(Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct ExternConstraintDeclaration<'a> {
    pub nodes: (
        Option<Static<'a>>,
        ClassScope<'a>,
        ConstraintIdentifier<'a>,
        ConstraintBlock<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct IdentifierList<'a> {
    pub nodes: (Vec<Identifier<'a>>,),
}

// -----------------------------------------------------------------------------

pub fn constraint_declaration(s: Span) -> IResult<Span, ConstraintDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn constraint_block(s: Span) -> IResult<Span, ConstraintBlock> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn constraint_block_item(s: Span) -> IResult<Span, ConstraintBlockItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn solve_before_list(s: Span) -> IResult<Span, SolveBeforeList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn constraint_primary(s: Span) -> IResult<Span, ConstraintPrimary> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn constraint_expression(s: Span) -> IResult<Span, ConstraintExpression> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn uniqueness_constraint(s: Span) -> IResult<Span, UniquenessConstraint> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn constraint_set(s: Span) -> IResult<Span, ConstraintSet> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn dist_list(s: Span) -> IResult<Span, DistList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn dist_item(s: Span) -> IResult<Span, DistItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn dist_weight(s: Span) -> IResult<Span, DistWeight> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn constraint_prototype(s: Span) -> IResult<Span, ConstraintPrototype> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn constraint_prototype_qualifier(s: Span) -> IResult<Span, ConstraintPrototypeQualifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn extern_constraint_declaration(s: Span) -> IResult<Span, ExternConstraintDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn identifier_list(s: Span) -> IResult<Span, IdentifierList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}
