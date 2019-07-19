use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct ConstraintDeclaration<'a> {
    pub nodes: (
        Option<Static<'a>>,
        Keyword<'a>,
        ConstraintIdentifier<'a>,
        ConstraintBlock<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct Static<'a> {
    pub nodes: (Keyword<'a>,),
}

#[derive(Debug, Node)]
pub struct ConstraintBlock<'a> {
    pub nodes: (Brace<'a, Vec<ConstraintBlockItem<'a>>>,),
}

#[derive(Debug, Node)]
pub enum ConstraintBlockItem<'a> {
    Solve(ConstraintBlockItemSolve<'a>),
    ConstraintExpression(ConstraintExpression<'a>),
}

#[derive(Debug, Node)]
pub struct ConstraintBlockItemSolve<'a> {
    pub nodes: (
        Keyword<'a>,
        SolveBeforeList<'a>,
        Keyword<'a>,
        SolveBeforeList<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct SolveBeforeList<'a> {
    pub nodes: (List<Symbol<'a>, ConstraintPrimary<'a>>,),
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
    UniquenessConstraint((UniquenessConstraint<'a>, Symbol<'a>)),
    Arrow(ConstraintExpressionArrow<'a>),
    If(ConstraintExpressionIf<'a>),
    Foreach(ConstraintExpressionForeach<'a>),
    Disable(ConstraintExpressionDisable<'a>),
}

#[derive(Debug, Node)]
pub struct ConstraintExpressionExpression<'a> {
    pub nodes: (Option<Soft<'a>>, ExpressionOrDist<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct Soft<'a> {
    pub nodes: (Keyword<'a>,),
}

#[derive(Debug, Node)]
pub struct ConstraintExpressionArrow<'a> {
    pub nodes: (Expression<'a>, Symbol<'a>, ConstraintSet<'a>),
}

#[derive(Debug, Node)]
pub struct ConstraintExpressionIf<'a> {
    pub nodes: (
        Keyword<'a>,
        Paren<'a, Expression<'a>>,
        ConstraintSet<'a>,
        Option<(Keyword<'a>, ConstraintSet<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct ConstraintExpressionForeach<'a> {
    pub nodes: (
        Keyword<'a>,
        Paren<
            'a,
            (
                PsOrHierarchicalArrayIdentifier<'a>,
                Bracket<'a, LoopVariables<'a>>,
            ),
        >,
        ConstraintSet<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ConstraintExpressionDisable<'a> {
    pub nodes: (Keyword<'a>, Keyword<'a>, ConstraintPrimary<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct UniquenessConstraint<'a> {
    pub nodes: (Keyword<'a>, Brace<'a, OpenRangeList<'a>>),
}

#[derive(Debug, Node)]
pub enum ConstraintSet<'a> {
    ConstraintExpression(Box<ConstraintExpression<'a>>),
    Brace(ConstraintSetBrace<'a>),
}

#[derive(Debug, Node)]
pub struct ConstraintSetBrace<'a> {
    pub nodes: (Brace<'a, Vec<ConstraintExpression<'a>>>,),
}

#[derive(Debug, Node)]
pub struct DistList<'a> {
    pub nodes: (List<Symbol<'a>, DistItem<'a>>,),
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
    pub nodes: (Symbol<'a>, Expression<'a>),
}

#[derive(Debug, Node)]
pub struct DistWeightDivide<'a> {
    pub nodes: (Symbol<'a>, Expression<'a>),
}

#[derive(Debug, Node)]
pub struct ConstraintPrototype<'a> {
    pub nodes: (
        Option<ConstraintPrototypeQualifier<'a>>,
        Option<Static<'a>>,
        Keyword<'a>,
        ConstraintIdentifier<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum ConstraintPrototypeQualifier<'a> {
    Extern(Keyword<'a>),
    Pure(Keyword<'a>),
}

#[derive(Debug, Node)]
pub struct ExternConstraintDeclaration<'a> {
    pub nodes: (
        Option<Static<'a>>,
        Keyword<'a>,
        ClassScope<'a>,
        ConstraintIdentifier<'a>,
        ConstraintBlock<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct IdentifierList<'a> {
    pub nodes: (List<Symbol<'a>, Identifier<'a>>,),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn constraint_declaration(s: Span) -> IResult<Span, ConstraintDeclaration> {
    let (s, a) = opt(r#static)(s)?;
    let (s, b) = keyword("constraint")(s)?;
    let (s, c) = constraint_identifier(s)?;
    let (s, d) = constraint_block(s)?;
    Ok((
        s,
        ConstraintDeclaration {
            nodes: (a, b, c, d),
        },
    ))
}

#[parser]
pub fn r#static(s: Span) -> IResult<Span, Static> {
    let (s, a) = keyword("static")(s)?;
    Ok((s, Static { nodes: (a,) }))
}

#[parser]
pub fn constraint_block(s: Span) -> IResult<Span, ConstraintBlock> {
    let (s, a) = brace(many0(constraint_block_item))(s)?;
    Ok((s, ConstraintBlock { nodes: (a,) }))
}

#[parser]
pub fn constraint_block_item(s: Span) -> IResult<Span, ConstraintBlockItem> {
    alt((
        constraint_block_item_solve,
        map(constraint_expression, |x| {
            ConstraintBlockItem::ConstraintExpression(x)
        }),
    ))(s)
}

#[parser]
pub fn constraint_block_item_solve(s: Span) -> IResult<Span, ConstraintBlockItem> {
    let (s, a) = keyword("solve")(s)?;
    let (s, b) = solve_before_list(s)?;
    let (s, c) = keyword("before")(s)?;
    let (s, d) = solve_before_list(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        ConstraintBlockItem::Solve(ConstraintBlockItemSolve {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn solve_before_list(s: Span) -> IResult<Span, SolveBeforeList> {
    let (s, a) = list(symbol(","), constraint_primary)(s)?;
    Ok((s, SolveBeforeList { nodes: (a,) }))
}

#[parser]
pub fn constraint_primary(s: Span) -> IResult<Span, ConstraintPrimary> {
    let (s, a) = opt(implicit_class_handle_or_class_scope)(s)?;
    let (s, b) = hierarchical_identifier(s)?;
    let (s, c) = select(s)?;
    Ok((s, ConstraintPrimary { nodes: (a, b, c) }))
}

#[parser]
pub fn constraint_expression(s: Span) -> IResult<Span, ConstraintExpression> {
    alt((
        constraint_expression_expression,
        map(pair(uniqueness_constraint, symbol(";")), |x| {
            ConstraintExpression::UniquenessConstraint(x)
        }),
        constraint_expression_arrow,
        constraint_expression_if,
        constraint_expression_foreach,
        constraint_expression_disable,
    ))(s)
}

#[parser(MaybeRecursive)]
pub fn constraint_expression_expression(s: Span) -> IResult<Span, ConstraintExpression> {
    let (s, a) = opt(soft)(s)?;
    let (s, b) = expression_or_dist(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ConstraintExpression::Expression(ConstraintExpressionExpression { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn soft(s: Span) -> IResult<Span, Soft> {
    let (s, a) = keyword("soft")(s)?;
    Ok((s, Soft { nodes: (a,) }))
}

#[parser(MaybeRecursive)]
pub fn constraint_expression_arrow(s: Span) -> IResult<Span, ConstraintExpression> {
    let (s, a) = expression(s)?;
    let (s, b) = symbol("->")(s)?;
    let (s, c) = constraint_set(s)?;
    Ok((
        s,
        ConstraintExpression::Arrow(ConstraintExpressionArrow { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn constraint_expression_if(s: Span) -> IResult<Span, ConstraintExpression> {
    let (s, a) = keyword("if")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = constraint_set(s)?;
    let (s, d) = opt(pair(keyword("else"), constraint_set))(s)?;
    Ok((
        s,
        ConstraintExpression::If(ConstraintExpressionIf {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn constraint_expression_foreach(s: Span) -> IResult<Span, ConstraintExpression> {
    let (s, a) = keyword("foreach")(s)?;
    let (s, b) = paren(pair(
        ps_or_hierarchical_array_identifier,
        bracket(loop_variables),
    ))(s)?;
    let (s, c) = constraint_set(s)?;
    Ok((
        s,
        ConstraintExpression::Foreach(ConstraintExpressionForeach { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn constraint_expression_disable(s: Span) -> IResult<Span, ConstraintExpression> {
    let (s, a) = keyword("disable")(s)?;
    let (s, b) = keyword("soft")(s)?;
    let (s, c) = constraint_primary(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        ConstraintExpression::Disable(ConstraintExpressionDisable {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn uniqueness_constraint(s: Span) -> IResult<Span, UniquenessConstraint> {
    let (s, a) = keyword("unique")(s)?;
    let (s, b) = brace(open_range_list)(s)?;
    Ok((s, UniquenessConstraint { nodes: (a, b) }))
}

#[parser]
pub fn constraint_set(s: Span) -> IResult<Span, ConstraintSet> {
    alt((
        map(constraint_expression, |x| {
            ConstraintSet::ConstraintExpression(Box::new(x))
        }),
        constraint_set_brace,
    ))(s)
}

#[parser]
pub fn constraint_set_brace(s: Span) -> IResult<Span, ConstraintSet> {
    let (s, a) = brace(many0(constraint_expression))(s)?;
    Ok((s, ConstraintSet::Brace(ConstraintSetBrace { nodes: (a,) })))
}

#[parser(MaybeRecursive)]
pub fn dist_list(s: Span) -> IResult<Span, DistList> {
    let (s, a) = list(symbol(","), dist_item)(s)?;
    Ok((s, DistList { nodes: (a,) }))
}

#[parser(MaybeRecursive)]
pub fn dist_item(s: Span) -> IResult<Span, DistItem> {
    let (s, a) = value_range(s)?;
    let (s, b) = opt(dist_weight)(s)?;
    Ok((s, DistItem { nodes: (a, b) }))
}

#[parser]
pub fn dist_weight(s: Span) -> IResult<Span, DistWeight> {
    alt((dist_weight_equal, dist_weight_divide))(s)
}

#[parser]
pub fn dist_weight_equal(s: Span) -> IResult<Span, DistWeight> {
    let (s, a) = symbol(":=")(s)?;
    let (s, b) = expression(s)?;
    Ok((s, DistWeight::Equal(DistWeightEqual { nodes: (a, b) })))
}

#[parser]
pub fn dist_weight_divide(s: Span) -> IResult<Span, DistWeight> {
    let (s, a) = symbol(":/")(s)?;
    let (s, b) = expression(s)?;
    Ok((s, DistWeight::Divide(DistWeightDivide { nodes: (a, b) })))
}

#[parser]
pub fn constraint_prototype(s: Span) -> IResult<Span, ConstraintPrototype> {
    let (s, a) = opt(constraint_prototype_qualifier)(s)?;
    let (s, b) = opt(r#static)(s)?;
    let (s, c) = keyword("constraint")(s)?;
    let (s, d) = constraint_identifier(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        ConstraintPrototype {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser]
pub fn constraint_prototype_qualifier(s: Span) -> IResult<Span, ConstraintPrototypeQualifier> {
    alt((
        map(keyword("extern"), |x| {
            ConstraintPrototypeQualifier::Extern(x)
        }),
        map(keyword("pure"), |x| ConstraintPrototypeQualifier::Pure(x)),
    ))(s)
}

#[parser]
pub fn extern_constraint_declaration(s: Span) -> IResult<Span, ExternConstraintDeclaration> {
    let (s, a) = opt(r#static)(s)?;
    let (s, b) = keyword("constraint")(s)?;
    let (s, c) = class_scope(s)?;
    let (s, d) = constraint_identifier(s)?;
    let (s, e) = constraint_block(s)?;
    Ok((
        s,
        ExternConstraintDeclaration {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser]
pub fn identifier_list(s: Span) -> IResult<Span, IdentifierList> {
    let (s, a) = list(symbol(","), identifier)(s)?;
    Ok((s, IdentifierList { nodes: (a,) }))
}
