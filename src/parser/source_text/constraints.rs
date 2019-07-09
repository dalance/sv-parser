use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct ConstraintDeclaration<'a> {
    pub nodes: (
        Option<Static>,
        ConstraintIdentifier<'a>,
        ConstraintBlock<'a>,
    ),
}

#[derive(Debug)]
pub struct Static {}

#[derive(Debug)]
pub struct ConstraintBlock<'a> {
    pub nodes: (Vec<ConstraintBlockItem<'a>>,),
}

#[derive(Debug)]
pub enum ConstraintBlockItem<'a> {
    Solve(ConstraintBlockItemSolve<'a>),
    ConstraintExpression(ConstraintExpression<'a>),
}

#[derive(Debug)]
pub struct ConstraintBlockItemSolve<'a> {
    pub nodes: (SolveBeforeList<'a>, SolveBeforeList<'a>),
}

#[derive(Debug)]
pub struct SolveBeforeList<'a> {
    pub nodes: (Vec<ConstraintPrimary<'a>>,),
}

#[derive(Debug)]
pub struct ConstraintPrimary<'a> {
    pub nodes: (
        Option<ImplicitClassHandleOrClassScope<'a>>,
        HierarchicalIdentifier<'a>,
        Select<'a>,
    ),
}

#[derive(Debug)]
pub enum ConstraintExpression<'a> {
    Expression(ConstraintExpressionExpression<'a>),
    UniquenessConstraint(UniquenessConstraint<'a>),
    Arrow(ConstraintExpressionArrow<'a>),
    If(ConstraintExpressionIf<'a>),
    Foreach(ConstraintExpressionForeach<'a>),
    Disable(ConstraintExpressionDisable<'a>),
}

#[derive(Debug)]
pub struct ConstraintExpressionExpression<'a> {
    pub nodes: (Option<Soft>, ExpressionOrDist<'a>),
}

#[derive(Debug)]
pub struct Soft {}

#[derive(Debug)]
pub struct ConstraintExpressionArrow<'a> {
    pub nodes: (Expression<'a>, ConstraintSet<'a>),
}

#[derive(Debug)]
pub struct ConstraintExpressionIf<'a> {
    pub nodes: (Expression<'a>, ConstraintSet<'a>, Option<ConstraintSet<'a>>),
}

#[derive(Debug)]
pub struct ConstraintExpressionForeach<'a> {
    pub nodes: (
        PsOrHierarchicalArrayIdentifier<'a>,
        LoopVariables<'a>,
        ConstraintSet<'a>,
    ),
}

#[derive(Debug)]
pub struct ConstraintExpressionDisable<'a> {
    pub nodes: (ConstraintPrimary<'a>,),
}

#[derive(Debug)]
pub struct UniquenessConstraint<'a> {
    pub nodes: (OpenRangeList<'a>,),
}

#[derive(Debug)]
pub enum ConstraintSet<'a> {
    ConstraintExpression(Box<ConstraintExpression<'a>>),
    Bracket(ConstraintSetBracket<'a>),
}

#[derive(Debug)]
pub struct ConstraintSetBracket<'a> {
    pub nodes: (Vec<ConstraintExpression<'a>>,),
}

#[derive(Debug)]
pub struct DistList<'a> {
    pub nodes: (Vec<DistItem<'a>>,),
}

#[derive(Debug)]
pub struct DistItem<'a> {
    pub nodes: (ValueRange<'a>, Option<DistWeight<'a>>),
}

#[derive(Debug)]
pub enum DistWeight<'a> {
    Equal(DistWeightEqual<'a>),
    Divide(DistWeightDivide<'a>),
}

#[derive(Debug)]
pub struct DistWeightEqual<'a> {
    pub nodes: (Expression<'a>,),
}

#[derive(Debug)]
pub struct DistWeightDivide<'a> {
    pub nodes: (Expression<'a>,),
}

#[derive(Debug)]
pub struct ConstraintPrototype<'a> {
    pub nodes: (
        Option<ConstraintPrototypeQualifier>,
        Option<Static>,
        ConstraintIdentifier<'a>,
    ),
}

#[derive(Debug)]
pub enum ConstraintPrototypeQualifier {
    Extern,
    Pure,
}

#[derive(Debug)]
pub struct ExternConstraintDeclaration<'a> {
    pub nodes: (
        Option<Static>,
        ClassScope<'a>,
        ConstraintIdentifier<'a>,
        ConstraintBlock<'a>,
    ),
}

#[derive(Debug)]
pub struct IdentifierList<'a> {
    pub nodes: (Vec<Identifier<'a>>,),
}

// -----------------------------------------------------------------------------

pub fn constraint_declaration(s: &str) -> IResult<&str, ConstraintDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn constraint_block(s: &str) -> IResult<&str, ConstraintBlock> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn constraint_block_item(s: &str) -> IResult<&str, ConstraintBlockItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn solve_before_list(s: &str) -> IResult<&str, SolveBeforeList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn constraint_primary(s: &str) -> IResult<&str, ConstraintPrimary> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn constraint_expression(s: &str) -> IResult<&str, ConstraintExpression> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn uniqueness_constraint(s: &str) -> IResult<&str, UniquenessConstraint> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn constraint_set(s: &str) -> IResult<&str, ConstraintSet> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn dist_list(s: &str) -> IResult<&str, DistList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn dist_item(s: &str) -> IResult<&str, DistItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn dist_weight(s: &str) -> IResult<&str, DistWeight> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn constraint_prototype(s: &str) -> IResult<&str, ConstraintPrototype> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn constraint_prototype_qualifier(s: &str) -> IResult<&str, ConstraintPrototypeQualifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn extern_constraint_declaration(s: &str) -> IResult<&str, ExternConstraintDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn identifier_list(s: &str) -> IResult<&str, IdentifierList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}
