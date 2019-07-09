use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct GenerateRegion<'a> {
    pub nodes: (Vec<GenerateItem<'a>>,),
}

#[derive(Debug)]
pub struct LoopGenerateConstruct<'a> {
    pub nodes: (
        GenvarInitialization<'a>,
        ConstantExpression<'a>,
        GenvarIteration<'a>,
        GenerateBlock<'a>,
    ),
}

#[derive(Debug)]
pub struct GenvarInitialization<'a> {
    pub nodes: (Option<Genvar>, GenvarIdentifier<'a>, ConstantExpression<'a>),
}

#[derive(Debug)]
pub struct Genvar {}

#[derive(Debug)]
pub enum GenvarIteration<'a> {
    Assignment(GenvarIterationAssignment<'a>),
    Prefix(GenvarIterationPrefix<'a>),
    Suffix(GenvarIterationSuffix<'a>),
}

#[derive(Debug)]
pub struct GenvarIterationAssignment<'a> {
    pub nodes: (
        GenvarIdentifier<'a>,
        AssignmentOperator<'a>,
        ConstantExpression<'a>,
    ),
}

#[derive(Debug)]
pub struct GenvarIterationPrefix<'a> {
    pub nodes: (IncOrDecOperator<'a>, GenvarIdentifier<'a>),
}

#[derive(Debug)]
pub struct GenvarIterationSuffix<'a> {
    pub nodes: (GenvarIdentifier<'a>, IncOrDecOperator<'a>),
}

#[derive(Debug)]
pub enum ConditionalGenerateConstruct<'a> {
    If(IfGenerateConstruct<'a>),
    Case(CaseGenerateConstruct<'a>),
}

#[derive(Debug)]
pub struct IfGenerateConstruct<'a> {
    pub nodes: (
        ConstantExpression<'a>,
        GenerateBlock<'a>,
        Option<GenerateBlock<'a>>,
    ),
}

#[derive(Debug)]
pub struct CaseGenerateConstruct<'a> {
    pub nodes: (ConstantExpression<'a>, Vec<CaseGenerateItem<'a>>),
}

#[derive(Debug)]
pub enum CaseGenerateItem<'a> {
    Nondefault(CaseGenerateItemNondefault<'a>),
    Default(CaseGenerateItemDefault<'a>),
}

#[derive(Debug)]
pub struct CaseGenerateItemNondefault<'a> {
    pub nodes: (Vec<ConstantExpression<'a>>, GenerateBlock<'a>),
}

#[derive(Debug)]
pub struct CaseGenerateItemDefault<'a> {
    pub nodes: (GenerateBlock<'a>,),
}

#[derive(Debug)]
pub enum GenerateBlock<'a> {
    Single(GenerateItem<'a>),
    Multiple(GenerateBlockMultiple<'a>),
}

#[derive(Debug)]
pub struct GenerateBlockMultiple<'a> {
    pub nodes: (
        Option<GenerateBlockIdentifier<'a>>,
        Option<GenerateBlockIdentifier<'a>>,
        Vec<GenerateItem<'a>>,
        Option<GenerateBlockIdentifier<'a>>,
    ),
}

#[derive(Debug)]
pub enum GenerateItem<'a> {
    Module(ModuleOrGenerateItem<'a>),
    Interface(InterfaceOrGenerateItem<'a>),
    Checker(CheckerOrGenerateItem<'a>),
}

// -----------------------------------------------------------------------------

pub fn generate_region(s: Span) -> IResult<Span, GenerateRegion> {
    let (s, _) = symbol("generate")(s)?;
    let (s, x) = many0(generate_item)(s)?;
    let (s, _) = symbol("endgenerate")(s)?;
    Ok((s, GenerateRegion { nodes: (x,) }))
}

pub fn loop_generate_construct(s: Span) -> IResult<Span, LoopGenerateConstruct> {
    let (s, _) = symbol("for")(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, x) = generate_initialization(s)?;
    let (s, _) = symbol(";")(s)?;
    let (s, y) = genvar_expression(s)?;
    let (s, _) = symbol(";")(s)?;
    let (s, z) = genvar_iteration(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, v) = generate_block(s)?;
    Ok((
        s,
        LoopGenerateConstruct {
            nodes: (x, y, z, v),
        },
    ))
}

pub fn generate_initialization(s: Span) -> IResult<Span, GenvarInitialization> {
    let (s, x) = opt(symbol("genvar"))(s)?;
    let (s, y) = genvar_identifier(s)?;
    let (s, _) = symbol("=")(s)?;
    let (s, z) = constant_expression(s)?;
    Ok((
        s,
        GenvarInitialization {
            nodes: (x.map(|_| Genvar {}), y, z),
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
    let (s, x) = genvar_identifier(s)?;
    let (s, y) = assignment_operator(s)?;
    let (s, z) = genvar_expression(s)?;
    Ok((
        s,
        GenvarIteration::Assignment(GenvarIterationAssignment { nodes: (x, y, z) }),
    ))
}

pub fn genvar_iteration_prefix(s: Span) -> IResult<Span, GenvarIteration> {
    let (s, x) = inc_or_dec_operator(s)?;
    let (s, y) = genvar_identifier(s)?;
    Ok((
        s,
        GenvarIteration::Prefix(GenvarIterationPrefix { nodes: (x, y) }),
    ))
}

pub fn genvar_iteration_suffix(s: Span) -> IResult<Span, GenvarIteration> {
    let (s, x) = genvar_identifier(s)?;
    let (s, y) = inc_or_dec_operator(s)?;
    Ok((
        s,
        GenvarIteration::Suffix(GenvarIterationSuffix { nodes: (x, y) }),
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
    let (s, _) = symbol("if")(s)?;
    let (s, x) = paren(constant_expression)(s)?;
    let (s, y) = generate_block(s)?;
    let (s, z) = opt(preceded(symbol("else"), generate_block))(s)?;
    Ok((s, IfGenerateConstruct { nodes: (x, y, z) }))
}

pub fn case_generate_construct(s: Span) -> IResult<Span, CaseGenerateConstruct> {
    let (s, _) = symbol("case")(s)?;
    let (s, x) = paren(constant_expression)(s)?;
    let (s, y) = many1(case_generate_item)(s)?;
    let (s, _) = symbol("endcase")(s)?;
    Ok((s, CaseGenerateConstruct { nodes: (x, y) }))
}

pub fn case_generate_item(s: Span) -> IResult<Span, CaseGenerateItem> {
    alt((case_generate_item_nondefault, case_generate_item_default))(s)
}

pub fn case_generate_item_nondefault(s: Span) -> IResult<Span, CaseGenerateItem> {
    let (s, x) = separated_nonempty_list(symbol(","), constant_expression)(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, y) = generate_block(s)?;
    Ok((
        s,
        CaseGenerateItem::Nondefault(CaseGenerateItemNondefault { nodes: (x, y) }),
    ))
}

pub fn case_generate_item_default(s: Span) -> IResult<Span, CaseGenerateItem> {
    let (s, _) = symbol("default")(s)?;
    let (s, _) = opt(symbol(":"))(s)?;
    let (s, x) = generate_block(s)?;
    Ok((
        s,
        CaseGenerateItem::Default(CaseGenerateItemDefault { nodes: (x,) }),
    ))
}

pub fn generate_block(s: Span) -> IResult<Span, GenerateBlock> {
    alt((generate_block_single, generate_block_multiple))(s)
}

pub fn generate_block_single(s: Span) -> IResult<Span, GenerateBlock> {
    let (s, x) = generate_item(s)?;
    Ok((s, GenerateBlock::Single(x)))
}

pub fn generate_block_multiple(s: Span) -> IResult<Span, GenerateBlock> {
    let (s, x) = opt(terminated(generate_block_identifier, symbol(":")))(s)?;
    let (s, _) = symbol("begin")(s)?;
    let (s, y) = opt(preceded(symbol(":"), generate_block_identifier))(s)?;
    let (s, z) = many0(generate_item)(s)?;
    let (s, _) = symbol("end")(s)?;
    let (s, v) = opt(preceded(symbol(":"), generate_block_identifier))(s)?;
    Ok((
        s,
        GenerateBlock::Multiple(GenerateBlockMultiple {
            nodes: (x, y, z, v),
        }),
    ))
}

pub fn generate_item(s: Span) -> IResult<Span, GenerateItem> {
    alt((
        map(module_or_generate_item, |x| GenerateItem::Module(x)),
        map(interface_or_generate_item, |x| GenerateItem::Interface(x)),
        map(checker_or_generate_item, |x| GenerateItem::Checker(x)),
    ))(s)
}

// -----------------------------------------------------------------------------
