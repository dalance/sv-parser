use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn constraint_declaration(s: Span) -> IResult<Span, ConstraintDeclaration> {
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

#[tracable_parser]
pub(crate) fn r#static(s: Span) -> IResult<Span, Static> {
    let (s, a) = keyword("static")(s)?;
    Ok((s, Static { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn constraint_block(s: Span) -> IResult<Span, ConstraintBlock> {
    let (s, a) = brace(many0(constraint_block_item))(s)?;
    Ok((s, ConstraintBlock { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn constraint_block_item(s: Span) -> IResult<Span, ConstraintBlockItem> {
    alt((
        constraint_block_item_solve,
        map(constraint_expression, |x| {
            ConstraintBlockItem::ConstraintExpression(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn constraint_block_item_solve(s: Span) -> IResult<Span, ConstraintBlockItem> {
    let (s, a) = keyword("solve")(s)?;
    let (s, b) = solve_before_list(s)?;
    let (s, c) = keyword("before")(s)?;
    let (s, d) = solve_before_list(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        ConstraintBlockItem::Solve(Box::new(ConstraintBlockItemSolve {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn solve_before_list(s: Span) -> IResult<Span, SolveBeforeList> {
    let (s, a) = list(symbol(","), constraint_primary)(s)?;
    Ok((s, SolveBeforeList { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn constraint_primary(s: Span) -> IResult<Span, ConstraintPrimary> {
    let (s, a) = opt(implicit_class_handle_or_class_scope)(s)?;
    let (s, b) = hierarchical_identifier(s)?;
    let (s, c) = select(s)?;
    Ok((s, ConstraintPrimary { nodes: (a, b, c) }))
}

#[tracable_parser]
pub(crate) fn constraint_expression(s: Span) -> IResult<Span, ConstraintExpression> {
    alt((
        constraint_expression_expression,
        map(pair(uniqueness_constraint, symbol(";")), |x| {
            ConstraintExpression::UniquenessConstraint(Box::new(x))
        }),
        constraint_expression_arrow,
        constraint_expression_if,
        constraint_expression_foreach,
        constraint_expression_disable,
    ))(s)
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn constraint_expression_expression(s: Span) -> IResult<Span, ConstraintExpression> {
    let (s, a) = opt(soft)(s)?;
    let (s, b) = expression_or_dist(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ConstraintExpression::Expression(Box::new(ConstraintExpressionExpression {
            nodes: (a, b, c),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn soft(s: Span) -> IResult<Span, Soft> {
    let (s, a) = keyword("soft")(s)?;
    Ok((s, Soft { nodes: (a,) }))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn constraint_expression_arrow(s: Span) -> IResult<Span, ConstraintExpression> {
    let (s, a) = expression(s)?;
    let (s, b) = symbol("->")(s)?;
    let (s, c) = constraint_set(s)?;
    Ok((
        s,
        ConstraintExpression::Arrow(Box::new(ConstraintExpressionArrow { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn constraint_expression_if(s: Span) -> IResult<Span, ConstraintExpression> {
    let (s, a) = keyword("if")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = constraint_set(s)?;
    let (s, d) = opt(pair(keyword("else"), constraint_set))(s)?;
    Ok((
        s,
        ConstraintExpression::If(Box::new(ConstraintExpressionIf {
            nodes: (a, b, c, d),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn constraint_expression_foreach(s: Span) -> IResult<Span, ConstraintExpression> {
    let (s, a) = keyword("foreach")(s)?;
    let (s, b) = paren(pair(
        ps_or_hierarchical_array_identifier,
        bracket(loop_variables),
    ))(s)?;
    let (s, c) = constraint_set(s)?;
    Ok((
        s,
        ConstraintExpression::Foreach(Box::new(ConstraintExpressionForeach { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn constraint_expression_disable(s: Span) -> IResult<Span, ConstraintExpression> {
    let (s, a) = keyword("disable")(s)?;
    let (s, b) = keyword("soft")(s)?;
    let (s, c) = constraint_primary(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        ConstraintExpression::Disable(Box::new(ConstraintExpressionDisable {
            nodes: (a, b, c, d),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn uniqueness_constraint(s: Span) -> IResult<Span, UniquenessConstraint> {
    let (s, a) = keyword("unique")(s)?;
    let (s, b) = brace(open_range_list)(s)?;
    Ok((s, UniquenessConstraint { nodes: (a, b) }))
}

#[tracable_parser]
pub(crate) fn constraint_set(s: Span) -> IResult<Span, ConstraintSet> {
    alt((
        map(constraint_expression, |x| {
            ConstraintSet::ConstraintExpression(Box::new(x))
        }),
        constraint_set_brace,
    ))(s)
}

#[tracable_parser]
pub(crate) fn constraint_set_brace(s: Span) -> IResult<Span, ConstraintSet> {
    let (s, a) = brace(many0(constraint_expression))(s)?;
    Ok((
        s,
        ConstraintSet::Brace(Box::new(ConstraintSetBrace { nodes: (a,) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn dist_list(s: Span) -> IResult<Span, DistList> {
    let (s, a) = list(symbol(","), dist_item)(s)?;
    Ok((s, DistList { nodes: (a,) }))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn dist_item(s: Span) -> IResult<Span, DistItem> {
    let (s, a) = value_range(s)?;
    let (s, b) = opt(dist_weight)(s)?;
    Ok((s, DistItem { nodes: (a, b) }))
}

#[tracable_parser]
pub(crate) fn dist_weight(s: Span) -> IResult<Span, DistWeight> {
    alt((dist_weight_equal, dist_weight_divide))(s)
}

#[tracable_parser]
pub(crate) fn dist_weight_equal(s: Span) -> IResult<Span, DistWeight> {
    let (s, a) = symbol(":=")(s)?;
    let (s, b) = expression(s)?;
    Ok((
        s,
        DistWeight::Equal(Box::new(DistWeightEqual { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn dist_weight_divide(s: Span) -> IResult<Span, DistWeight> {
    let (s, a) = symbol(":/")(s)?;
    let (s, b) = expression(s)?;
    Ok((
        s,
        DistWeight::Divide(Box::new(DistWeightDivide { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn constraint_prototype(s: Span) -> IResult<Span, ConstraintPrototype> {
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

#[tracable_parser]
pub(crate) fn constraint_prototype_qualifier(
    s: Span,
) -> IResult<Span, ConstraintPrototypeQualifier> {
    alt((
        map(keyword("extern"), |x| {
            ConstraintPrototypeQualifier::Extern(Box::new(x))
        }),
        map(keyword("pure"), |x| {
            ConstraintPrototypeQualifier::Pure(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn extern_constraint_declaration(s: Span) -> IResult<Span, ExternConstraintDeclaration> {
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

#[tracable_parser]
pub(crate) fn identifier_list(s: Span) -> IResult<Span, IdentifierList> {
    let (s, a) = list(symbol(","), identifier)(s)?;
    Ok((s, IdentifierList { nodes: (a,) }))
}
