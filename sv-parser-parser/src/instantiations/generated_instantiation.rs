use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn generate_region(s: Span) -> IResult<Span, GenerateRegion> {
    let (s, a) = keyword("generate")(s)?;
    let (s, b) = many0(generate_item)(s)?;
    let (s, c) = keyword("endgenerate")(s)?;
    Ok((s, GenerateRegion { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn loop_generate_construct(s: Span) -> IResult<Span, LoopGenerateConstruct> {
    let (s, a) = keyword("for")(s)?;
    let (s, b) = paren(tuple((
        generate_initialization,
        symbol(";"),
        genvar_expression,
        symbol(";"),
        genvar_iteration,
    )))(s)?;
    let (s, c) = generate_block(s)?;
    Ok((s, LoopGenerateConstruct { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn generate_initialization(s: Span) -> IResult<Span, GenvarInitialization> {
    let (s, a) = opt(map(keyword("genvar"), |x| Genvar { nodes: (x,) }))(s)?;
    let (s, b) = genvar_identifier(s)?;
    let (s, c) = symbol("=")(s)?;
    let (s, d) = constant_expression(s)?;
    Ok((
        s,
        GenvarInitialization {
            nodes: (a, b, c, d),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn genvar_iteration(s: Span) -> IResult<Span, GenvarIteration> {
    alt((
        genvar_iteration_assignment,
        genvar_iteration_prefix,
        genvar_iteration_suffix,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn genvar_iteration_assignment(s: Span) -> IResult<Span, GenvarIteration> {
    let (s, a) = genvar_identifier(s)?;
    let (s, b) = assignment_operator(s)?;
    let (s, c) = genvar_expression(s)?;
    Ok((
        s,
        GenvarIteration::Assignment(Box::new(GenvarIterationAssignment { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn genvar_iteration_prefix(s: Span) -> IResult<Span, GenvarIteration> {
    let (s, a) = inc_or_dec_operator(s)?;
    let (s, b) = genvar_identifier(s)?;
    Ok((
        s,
        GenvarIteration::Prefix(Box::new(GenvarIterationPrefix { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn genvar_iteration_suffix(s: Span) -> IResult<Span, GenvarIteration> {
    let (s, a) = genvar_identifier(s)?;
    let (s, b) = inc_or_dec_operator(s)?;
    Ok((
        s,
        GenvarIteration::Suffix(Box::new(GenvarIterationSuffix { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn conditional_generate_construct(
    s: Span,
) -> IResult<Span, ConditionalGenerateConstruct> {
    alt((
        map(if_generate_construct, |x| {
            ConditionalGenerateConstruct::If(Box::new(x))
        }),
        map(case_generate_construct, |x| {
            ConditionalGenerateConstruct::Case(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn if_generate_construct(s: Span) -> IResult<Span, IfGenerateConstruct> {
    let (s, a) = keyword("if")(s)?;
    let (s, b) = paren(constant_expression)(s)?;
    let (s, c) = generate_block(s)?;
    let (s, d) = opt(pair(keyword("else"), generate_block))(s)?;
    Ok((
        s,
        IfGenerateConstruct {
            nodes: (a, b, c, d),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn case_generate_construct(s: Span) -> IResult<Span, CaseGenerateConstruct> {
    let (s, a) = keyword("case")(s)?;
    let (s, b) = paren(constant_expression)(s)?;
    let (s, c) = many1(case_generate_item)(s)?;
    let (s, d) = keyword("endcase")(s)?;
    Ok((
        s,
        CaseGenerateConstruct {
            nodes: (a, b, c, d),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn case_generate_item(s: Span) -> IResult<Span, CaseGenerateItem> {
    alt((case_generate_item_nondefault, case_generate_item_default))(s)
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn case_generate_item_nondefault(s: Span) -> IResult<Span, CaseGenerateItem> {
    let (s, a) = list(symbol(","), constant_expression)(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = generate_block(s)?;
    Ok((
        s,
        CaseGenerateItem::Nondefault(Box::new(CaseGenerateItemNondefault { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn case_generate_item_default(s: Span) -> IResult<Span, CaseGenerateItem> {
    let (s, a) = keyword("default")(s)?;
    let (s, b) = opt(symbol(":"))(s)?;
    let (s, c) = generate_block(s)?;
    Ok((
        s,
        CaseGenerateItem::Default(Box::new(CaseGenerateItemDefault { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn generate_block(s: Span) -> IResult<Span, GenerateBlock> {
    alt((
        map(generate_item, |x| GenerateBlock::GenerateItem(Box::new(x))),
        generate_block_multiple,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn generate_block_multiple(s: Span) -> IResult<Span, GenerateBlock> {
    let (s, a) = opt(pair(generate_block_identifier, symbol(":")))(s)?;
    let (s, b) = keyword("begin")(s)?;
    let (s, c) = opt(pair(symbol(":"), generate_block_identifier))(s)?;
    let (s, d) = many0(generate_item)(s)?;
    let (s, e) = keyword("end")(s)?;
    let (s, f) = opt(pair(symbol(":"), generate_block_identifier))(s)?;
    Ok((
        s,
        GenerateBlock::Multiple(Box::new(GenerateBlockMultiple {
            nodes: (a, b, c, d, e, f),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn generate_item(s: Span) -> IResult<Span, GenerateItem> {
    alt((
        map(module_or_generate_item, |x| {
            GenerateItem::ModuleOrGenerateItem(Box::new(x))
        }),
        map(interface_or_generate_item, |x| {
            GenerateItem::InterfaceOrGenerateItem(Box::new(x))
        }),
        map(checker_or_generate_item, |x| {
            GenerateItem::CheckerOrGenerateItem(Box::new(x))
        }),
    ))(s)
}
