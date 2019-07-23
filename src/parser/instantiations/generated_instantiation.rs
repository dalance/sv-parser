use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct GenerateRegion {
    pub nodes: (Keyword, Vec<GenerateItem>, Keyword),
}

#[derive(Debug, Node)]
pub struct LoopGenerateConstruct {
    pub nodes: (
        Keyword,
        Paren<
            
            (
                GenvarInitialization,
                Symbol,
                GenvarExpression,
                Symbol,
                GenvarIteration,
            ),
        >,
        GenerateBlock,
    ),
}

#[derive(Debug, Node)]
pub struct GenvarInitialization {
    pub nodes: (
        Option<Genvar>,
        GenvarIdentifier,
        Symbol,
        ConstantExpression,
    ),
}

#[derive(Debug, Node)]
pub struct Genvar {
    pub nodes: (Keyword,),
}

#[derive(Debug, Node)]
pub enum GenvarIteration {
    Assignment(GenvarIterationAssignment),
    Prefix(GenvarIterationPrefix),
    Suffix(GenvarIterationSuffix),
}

#[derive(Debug, Node)]
pub struct GenvarIterationAssignment {
    pub nodes: (
        GenvarIdentifier,
        AssignmentOperator,
        GenvarExpression,
    ),
}

#[derive(Debug, Node)]
pub struct GenvarIterationPrefix {
    pub nodes: (IncOrDecOperator, GenvarIdentifier),
}

#[derive(Debug, Node)]
pub struct GenvarIterationSuffix {
    pub nodes: (GenvarIdentifier, IncOrDecOperator),
}

#[derive(Debug, Node)]
pub enum ConditionalGenerateConstruct {
    If(IfGenerateConstruct),
    Case(CaseGenerateConstruct),
}

#[derive(Debug, Node)]
pub struct IfGenerateConstruct {
    pub nodes: (
        Keyword,
        Paren< ConstantExpression>,
        GenerateBlock,
        Option<(Keyword, GenerateBlock)>,
    ),
}

#[derive(Debug, Node)]
pub struct CaseGenerateConstruct {
    pub nodes: (
        Keyword,
        Paren< ConstantExpression>,
        Vec<CaseGenerateItem>,
        Keyword,
    ),
}

#[derive(Debug, Node)]
pub enum CaseGenerateItem {
    Nondefault(CaseGenerateItemNondefault),
    Default(CaseGenerateItemDefault),
}

#[derive(Debug, Node)]
pub struct CaseGenerateItemNondefault {
    pub nodes: (
        List<Symbol, ConstantExpression>,
        Symbol,
        GenerateBlock,
    ),
}

#[derive(Debug, Node)]
pub struct CaseGenerateItemDefault {
    pub nodes: (Keyword, Option<Symbol>, GenerateBlock),
}

#[derive(Debug, Node)]
pub enum GenerateBlock {
    GenerateItem(GenerateItem),
    Multiple(GenerateBlockMultiple),
}

#[derive(Debug, Node)]
pub struct GenerateBlockMultiple {
    pub nodes: (
        Option<(GenerateBlockIdentifier, Symbol)>,
        Keyword,
        Option<(Symbol, GenerateBlockIdentifier)>,
        Vec<GenerateItem>,
        Keyword,
        Option<(Symbol, GenerateBlockIdentifier)>,
    ),
}

#[derive(Debug, Node)]
pub enum GenerateItem {
    ModuleOrGenerateItem(ModuleOrGenerateItem),
    InterfaceOrGenerateItem(InterfaceOrGenerateItem),
    CheckerOrGenerateItem(CheckerOrGenerateItem),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn generate_region(s: Span) -> IResult<Span, GenerateRegion> {
    let (s, a) = keyword("generate")(s)?;
    let (s, b) = many0(generate_item)(s)?;
    let (s, c) = keyword("endgenerate")(s)?;
    Ok((s, GenerateRegion { nodes: (a, b, c) }))
}

#[parser]
pub fn loop_generate_construct(s: Span) -> IResult<Span, LoopGenerateConstruct> {
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

#[parser]
pub fn generate_initialization(s: Span) -> IResult<Span, GenvarInitialization> {
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

#[parser]
pub fn genvar_iteration(s: Span) -> IResult<Span, GenvarIteration> {
    alt((
        genvar_iteration_assignment,
        genvar_iteration_prefix,
        genvar_iteration_suffix,
    ))(s)
}

#[parser]
pub fn genvar_iteration_assignment(s: Span) -> IResult<Span, GenvarIteration> {
    let (s, a) = genvar_identifier(s)?;
    let (s, b) = assignment_operator(s)?;
    let (s, c) = genvar_expression(s)?;
    Ok((
        s,
        GenvarIteration::Assignment(GenvarIterationAssignment { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn genvar_iteration_prefix(s: Span) -> IResult<Span, GenvarIteration> {
    let (s, a) = inc_or_dec_operator(s)?;
    let (s, b) = genvar_identifier(s)?;
    Ok((
        s,
        GenvarIteration::Prefix(GenvarIterationPrefix { nodes: (a, b) }),
    ))
}

#[parser]
pub fn genvar_iteration_suffix(s: Span) -> IResult<Span, GenvarIteration> {
    let (s, a) = genvar_identifier(s)?;
    let (s, b) = inc_or_dec_operator(s)?;
    Ok((
        s,
        GenvarIteration::Suffix(GenvarIterationSuffix { nodes: (a, b) }),
    ))
}

#[parser]
pub fn conditional_generate_construct(s: Span) -> IResult<Span, ConditionalGenerateConstruct> {
    alt((
        map(if_generate_construct, |x| {
            ConditionalGenerateConstruct::If(x)
        }),
        map(case_generate_construct, |x| {
            ConditionalGenerateConstruct::Case(x)
        }),
    ))(s)
}

#[parser]
pub fn if_generate_construct(s: Span) -> IResult<Span, IfGenerateConstruct> {
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

#[parser]
pub fn case_generate_construct(s: Span) -> IResult<Span, CaseGenerateConstruct> {
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

#[parser]
pub fn case_generate_item(s: Span) -> IResult<Span, CaseGenerateItem> {
    alt((case_generate_item_nondefault, case_generate_item_default))(s)
}

#[parser(MaybeRecursive)]
pub fn case_generate_item_nondefault(s: Span) -> IResult<Span, CaseGenerateItem> {
    let (s, a) = list(symbol(","), constant_expression)(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = generate_block(s)?;
    Ok((
        s,
        CaseGenerateItem::Nondefault(CaseGenerateItemNondefault { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn case_generate_item_default(s: Span) -> IResult<Span, CaseGenerateItem> {
    let (s, a) = keyword("default")(s)?;
    let (s, b) = opt(symbol(":"))(s)?;
    let (s, c) = generate_block(s)?;
    Ok((
        s,
        CaseGenerateItem::Default(CaseGenerateItemDefault { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn generate_block(s: Span) -> IResult<Span, GenerateBlock> {
    alt((
        map(generate_item, |x| GenerateBlock::GenerateItem(x)),
        generate_block_multiple,
    ))(s)
}

#[parser]
pub fn generate_block_multiple(s: Span) -> IResult<Span, GenerateBlock> {
    let (s, a) = opt(pair(generate_block_identifier, symbol(":")))(s)?;
    let (s, b) = keyword("begin")(s)?;
    let (s, c) = opt(pair(symbol(":"), generate_block_identifier))(s)?;
    let (s, d) = many0(generate_item)(s)?;
    let (s, e) = keyword("end")(s)?;
    let (s, f) = opt(pair(symbol(":"), generate_block_identifier))(s)?;
    Ok((
        s,
        GenerateBlock::Multiple(GenerateBlockMultiple {
            nodes: (a, b, c, d, e, f),
        }),
    ))
}

#[parser]
pub fn generate_item(s: Span) -> IResult<Span, GenerateItem> {
    alt((
        map(module_or_generate_item, |x| {
            GenerateItem::ModuleOrGenerateItem(x)
        }),
        map(interface_or_generate_item, |x| {
            GenerateItem::InterfaceOrGenerateItem(x)
        }),
        map(checker_or_generate_item, |x| {
            GenerateItem::CheckerOrGenerateItem(x)
        }),
    ))(s)
}

// -----------------------------------------------------------------------------
