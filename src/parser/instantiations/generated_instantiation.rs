use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct GenerateRegion<'a> {
    pub nodes: (Symbol<'a>, Vec<GenerateItem<'a>>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct LoopGenerateConstruct<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<
            'a,
            (
                GenvarInitialization<'a>,
                Symbol<'a>,
                GenvarExpression<'a>,
                Symbol<'a>,
                GenvarIteration<'a>,
            ),
        >,
        GenerateBlock<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct GenvarInitialization<'a> {
    pub nodes: (
        Option<Genvar<'a>>,
        GenvarIdentifier<'a>,
        Symbol<'a>,
        ConstantExpression<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct Genvar<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub enum GenvarIteration<'a> {
    Assignment(GenvarIterationAssignment<'a>),
    Prefix(GenvarIterationPrefix<'a>),
    Suffix(GenvarIterationSuffix<'a>),
}

#[derive(Debug, Node)]
pub struct GenvarIterationAssignment<'a> {
    pub nodes: (
        GenvarIdentifier<'a>,
        AssignmentOperator<'a>,
        GenvarExpression<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct GenvarIterationPrefix<'a> {
    pub nodes: (IncOrDecOperator<'a>, GenvarIdentifier<'a>),
}

#[derive(Debug, Node)]
pub struct GenvarIterationSuffix<'a> {
    pub nodes: (GenvarIdentifier<'a>, IncOrDecOperator<'a>),
}

#[derive(Debug, Node)]
pub enum ConditionalGenerateConstruct<'a> {
    If(IfGenerateConstruct<'a>),
    Case(CaseGenerateConstruct<'a>),
}

#[derive(Debug, Node)]
pub struct IfGenerateConstruct<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<'a, ConstantExpression<'a>>,
        GenerateBlock<'a>,
        Option<(Symbol<'a>, GenerateBlock<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct CaseGenerateConstruct<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<'a, ConstantExpression<'a>>,
        Vec<CaseGenerateItem<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum CaseGenerateItem<'a> {
    Nondefault(CaseGenerateItemNondefault<'a>),
    Default(CaseGenerateItemDefault<'a>),
}

#[derive(Debug, Node)]
pub struct CaseGenerateItemNondefault<'a> {
    pub nodes: (
        List<Symbol<'a>, ConstantExpression<'a>>,
        Symbol<'a>,
        GenerateBlock<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct CaseGenerateItemDefault<'a> {
    pub nodes: (Symbol<'a>, Option<Symbol<'a>>, GenerateBlock<'a>),
}

#[derive(Debug, Node)]
pub enum GenerateBlock<'a> {
    GenerateItem(GenerateItem<'a>),
    Multiple(GenerateBlockMultiple<'a>),
}

#[derive(Debug, Node)]
pub struct GenerateBlockMultiple<'a> {
    pub nodes: (
        Option<(GenerateBlockIdentifier<'a>, Symbol<'a>)>,
        Symbol<'a>,
        Option<(Symbol<'a>, GenerateBlockIdentifier<'a>)>,
        Vec<GenerateItem<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, GenerateBlockIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub enum GenerateItem<'a> {
    ModuleOrGenerateItem(ModuleOrGenerateItem<'a>),
    InterfaceOrGenerateItem(InterfaceOrGenerateItem<'a>),
    CheckerOrGenerateItem(CheckerOrGenerateItem<'a>),
}

// -----------------------------------------------------------------------------

pub fn generate_region(s: Span) -> IResult<Span, GenerateRegion> {
    let (s, a) = symbol("generate")(s)?;
    let (s, b) = many0(generate_item)(s)?;
    let (s, c) = symbol("endgenerate")(s)?;
    Ok((s, GenerateRegion { nodes: (a, b, c) }))
}

pub fn loop_generate_construct(s: Span) -> IResult<Span, LoopGenerateConstruct> {
    let (s, a) = symbol("for")(s)?;
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

pub fn generate_initialization(s: Span) -> IResult<Span, GenvarInitialization> {
    let (s, a) = opt(map(symbol("genvar"), |x| Genvar { nodes: (x,) }))(s)?;
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

pub fn genvar_iteration(s: Span) -> IResult<Span, GenvarIteration> {
    alt((
        genvar_iteration_assignment,
        genvar_iteration_prefix,
        genvar_iteration_suffix,
    ))(s)
}

pub fn genvar_iteration_assignment(s: Span) -> IResult<Span, GenvarIteration> {
    let (s, a) = genvar_identifier(s)?;
    let (s, b) = assignment_operator(s)?;
    let (s, c) = genvar_expression(s)?;
    Ok((
        s,
        GenvarIteration::Assignment(GenvarIterationAssignment { nodes: (a, b, c) }),
    ))
}

pub fn genvar_iteration_prefix(s: Span) -> IResult<Span, GenvarIteration> {
    let (s, a) = inc_or_dec_operator(s)?;
    let (s, b) = genvar_identifier(s)?;
    Ok((
        s,
        GenvarIteration::Prefix(GenvarIterationPrefix { nodes: (a, b) }),
    ))
}

pub fn genvar_iteration_suffix(s: Span) -> IResult<Span, GenvarIteration> {
    let (s, a) = genvar_identifier(s)?;
    let (s, b) = inc_or_dec_operator(s)?;
    Ok((
        s,
        GenvarIteration::Suffix(GenvarIterationSuffix { nodes: (a, b) }),
    ))
}

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

pub fn if_generate_construct(s: Span) -> IResult<Span, IfGenerateConstruct> {
    let (s, a) = symbol("if")(s)?;
    let (s, b) = paren(constant_expression)(s)?;
    let (s, c) = generate_block(s)?;
    let (s, d) = opt(pair(symbol("else"), generate_block))(s)?;
    Ok((
        s,
        IfGenerateConstruct {
            nodes: (a, b, c, d),
        },
    ))
}

pub fn case_generate_construct(s: Span) -> IResult<Span, CaseGenerateConstruct> {
    let (s, a) = symbol("case")(s)?;
    let (s, b) = paren(constant_expression)(s)?;
    let (s, c) = many1(case_generate_item)(s)?;
    let (s, d) = symbol("endcase")(s)?;
    Ok((
        s,
        CaseGenerateConstruct {
            nodes: (a, b, c, d),
        },
    ))
}

pub fn case_generate_item(s: Span) -> IResult<Span, CaseGenerateItem> {
    alt((case_generate_item_nondefault, case_generate_item_default))(s)
}

pub fn case_generate_item_nondefault(s: Span) -> IResult<Span, CaseGenerateItem> {
    let (s, a) = list(symbol(","), constant_expression)(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = generate_block(s)?;
    Ok((
        s,
        CaseGenerateItem::Nondefault(CaseGenerateItemNondefault { nodes: (a, b, c) }),
    ))
}

pub fn case_generate_item_default(s: Span) -> IResult<Span, CaseGenerateItem> {
    let (s, a) = symbol("default")(s)?;
    let (s, b) = opt(symbol(":"))(s)?;
    let (s, c) = generate_block(s)?;
    Ok((
        s,
        CaseGenerateItem::Default(CaseGenerateItemDefault { nodes: (a, b, c) }),
    ))
}

pub fn generate_block(s: Span) -> IResult<Span, GenerateBlock> {
    alt((
        map(generate_item, |x| GenerateBlock::GenerateItem(x)),
        generate_block_multiple,
    ))(s)
}

pub fn generate_block_multiple(s: Span) -> IResult<Span, GenerateBlock> {
    let (s, a) = opt(pair(generate_block_identifier, symbol(":")))(s)?;
    let (s, b) = symbol("begin")(s)?;
    let (s, c) = opt(pair(symbol(":"), generate_block_identifier))(s)?;
    let (s, d) = many0(generate_item)(s)?;
    let (s, e) = symbol("end")(s)?;
    let (s, f) = opt(pair(symbol(":"), generate_block_identifier))(s)?;
    Ok((
        s,
        GenerateBlock::Multiple(GenerateBlockMultiple {
            nodes: (a, b, c, d, e, f),
        }),
    ))
}

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
