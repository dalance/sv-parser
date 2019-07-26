use crate::*;

// -----------------------------------------------------------------------------

#[parser]
pub(crate) fn randsequence_statement(s: Span) -> IResult<Span, RandsequenceStatement> {
    let (s, a) = keyword("randsequence")(s)?;
    let (s, b) = paren(opt(production_identifier))(s)?;
    let (s, c) = production(s)?;
    let (s, d) = many0(production)(s)?;
    let (s, e) = keyword("endsequence")(s)?;
    Ok((
        s,
        RandsequenceStatement {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser]
pub(crate) fn production(s: Span) -> IResult<Span, Production> {
    let (s, a) = opt(data_type_or_void)(s)?;
    let (s, b) = production_identifier(s)?;
    let (s, c) = opt(paren(tf_port_list))(s)?;
    let (s, d) = symbol(":")(s)?;
    let (s, e) = list(symbol("|"), rs_rule)(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        Production {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

#[parser]
pub(crate) fn rs_rule(s: Span) -> IResult<Span, RsRule> {
    let (s, a) = rs_production_list(s)?;
    let (s, b) = opt(triple(
        symbol(":="),
        weight_specification,
        opt(rs_code_block),
    ))(s)?;
    Ok((s, RsRule { nodes: (a, b) }))
}

#[parser]
pub(crate) fn rs_production_list(s: Span) -> IResult<Span, RsProductionList> {
    alt((rs_production_list_prod, rs_production_list_join))(s)
}

#[parser]
pub(crate) fn rs_production_list_prod(s: Span) -> IResult<Span, RsProductionList> {
    let (s, a) = rs_prod(s)?;
    let (s, b) = many0(rs_prod)(s)?;
    Ok((
        s,
        RsProductionList::Prod(Box::new(RsProductionListProd { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn rs_production_list_join(s: Span) -> IResult<Span, RsProductionList> {
    let (s, a) = keyword("rand")(s)?;
    let (s, b) = keyword("join")(s)?;
    let (s, c) = opt(paren(expression))(s)?;
    let (s, d) = production_item(s)?;
    let (s, e) = production_item(s)?;
    let (s, f) = many0(production_item)(s)?;
    Ok((
        s,
        RsProductionList::Join(Box::new(RsProductionListJoin {
            nodes: (a, b, c, d, e, f),
        })),
    ))
}

#[parser]
pub(crate) fn weight_specification(s: Span) -> IResult<Span, WeightSpecification> {
    alt((
        map(integral_number, |x| {
            WeightSpecification::IntegralNumber(Box::new(x))
        }),
        map(ps_identifier, |x| {
            WeightSpecification::PsIdentifier(Box::new(x))
        }),
        weight_specification_expression,
    ))(s)
}

#[parser]
pub(crate) fn weight_specification_expression(s: Span) -> IResult<Span, WeightSpecification> {
    let (s, a) = paren(expression)(s)?;
    Ok((
        s,
        WeightSpecification::Expression(Box::new(WeightSpecificationExpression { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn rs_code_block(s: Span) -> IResult<Span, RsCodeBlock> {
    let (s, a) = brace(pair(many0(data_declaration), many0(statement_or_null)))(s)?;
    Ok((s, RsCodeBlock { nodes: (a,) }))
}

#[parser]
pub(crate) fn rs_prod(s: Span) -> IResult<Span, RsProd> {
    alt((
        map(production_item, |x| RsProd::ProductionItem(Box::new(x))),
        map(rs_code_block, |x| RsProd::RsCodeBlock(Box::new(x))),
        map(rs_if_else, |x| RsProd::RsIfElse(Box::new(x))),
        map(rs_repeat, |x| RsProd::RsRepeat(Box::new(x))),
        map(rs_case, |x| RsProd::RsCase(Box::new(x))),
    ))(s)
}

#[parser]
pub(crate) fn production_item(s: Span) -> IResult<Span, ProductionItem> {
    let (s, a) = production_identifier(s)?;
    let (s, b) = opt(paren(list_of_arguments))(s)?;
    Ok((s, ProductionItem { nodes: (a, b) }))
}

#[parser]
pub(crate) fn rs_if_else(s: Span) -> IResult<Span, RsIfElse> {
    let (s, a) = keyword("if")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = production_item(s)?;
    let (s, d) = opt(pair(keyword("else"), production_item))(s)?;
    Ok((
        s,
        RsIfElse {
            nodes: (a, b, c, d),
        },
    ))
}

#[parser]
pub(crate) fn rs_repeat(s: Span) -> IResult<Span, RsRepeat> {
    let (s, a) = keyword("repeat")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = production_item(s)?;
    Ok((s, RsRepeat { nodes: (a, b, c) }))
}

#[parser]
pub(crate) fn rs_case(s: Span) -> IResult<Span, RsCase> {
    let (s, a) = keyword("case")(s)?;
    let (s, b) = paren(case_expression)(s)?;
    let (s, c) = rs_case_item(s)?;
    let (s, d) = many0(rs_case_item)(s)?;
    let (s, e) = keyword("endcase")(s)?;
    Ok((
        s,
        RsCase {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser]
pub(crate) fn rs_case_item(s: Span) -> IResult<Span, RsCaseItem> {
    alt((rs_case_item_nondefault, rs_case_item_default))(s)
}

#[recursive_parser]
#[parser]
pub(crate) fn rs_case_item_nondefault(s: Span) -> IResult<Span, RsCaseItem> {
    let (s, a) = list(symbol(","), case_item_expression)(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = production_item(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        RsCaseItem::NonDefault(Box::new(RsCaseItemNondefault {
            nodes: (a, b, c, d),
        })),
    ))
}

#[parser]
pub(crate) fn rs_case_item_default(s: Span) -> IResult<Span, RsCaseItem> {
    let (s, a) = keyword("default")(s)?;
    let (s, b) = opt(symbol(":"))(s)?;
    let (s, c) = production_item(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        RsCaseItem::Default(Box::new(RsCaseItemDefault {
            nodes: (a, b, c, d),
        })),
    ))
}
