use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct CheckerPortList<'a> {
    pub nodes: (List<Symbol<'a>, CheckerPortItem<'a>>,),
}

#[derive(Debug, Node)]
pub struct CheckerPortItem<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Option<CheckerPortDirection<'a>>,
        PropertyFormalType<'a>,
        FormalPortIdentifier<'a>,
        Vec<VariableDimension<'a>>,
        Option<(Symbol<'a>, PropertyActualArg<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub enum CheckerPortDirection<'a> {
    Input(Symbol<'a>),
    Output(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum CheckerOrGenerateItem<'a> {
    CheckerOrGenerateItemDeclaration(CheckerOrGenerateItemDeclaration<'a>),
    InitialConstruct(InitialConstruct<'a>),
    AlwaysConstruct(AlwaysConstruct<'a>),
    FinalConstruct(FinalConstruct<'a>),
    AssertionItem(AssertionItem<'a>),
    ContinuousAssign(ContinuousAssign<'a>),
    CheckerGenerateItem(CheckerGenerateItem<'a>),
}

#[derive(Debug, Node)]
pub enum CheckerOrGenerateItemDeclaration<'a> {
    Data(CheckerOrGenerateItemDeclarationData<'a>),
    FunctionDeclaration(FunctionDeclaration<'a>),
    CheckerDeclaration(CheckerDeclaration<'a>),
    AssertionItemDeclaration(AssertionItemDeclaration<'a>),
    CovergroupDeclaration(CovergroupDeclaration<'a>),
    GenvarDeclaration(GenvarDeclaration<'a>),
    ClockingDeclaration(ClockingDeclaration<'a>),
    Clocking(CheckerOrGenerateItemDeclarationClocking<'a>),
    Disable(CheckerOrGenerateItemDeclarationDisable<'a>),
    Empty(Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct CheckerOrGenerateItemDeclarationData<'a> {
    pub nodes: (Option<Rand<'a>>, DataDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct Rand<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub struct CheckerOrGenerateItemDeclarationClocking<'a> {
    pub nodes: (Symbol<'a>, Symbol<'a>, ClockingIdentifier<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct CheckerOrGenerateItemDeclarationDisable<'a> {
    pub nodes: (
        Symbol<'a>,
        Symbol<'a>,
        Symbol<'a>,
        ExpressionOrDist<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum CheckerGenerateItem<'a> {
    LoopGenerateConstruct(Box<LoopGenerateConstruct<'a>>),
    ConditionalGenerateConstruct(Box<ConditionalGenerateConstruct<'a>>),
    GenerateRegion(GenerateRegion<'a>),
    ElaborationSystemTask(ElaborationSystemTask<'a>),
}

// -----------------------------------------------------------------------------

#[trace]
pub fn checker_port_list(s: Span) -> IResult<Span, CheckerPortList> {
    let (s, a) = list(symbol(","), checker_port_item)(s)?;
    Ok((s, CheckerPortList { nodes: (a,) }))
}

#[trace]
pub fn checker_port_item(s: Span) -> IResult<Span, CheckerPortItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = opt(checker_port_direction)(s)?;
    let (s, c) = property_formal_type(s)?;
    let (s, d) = formal_port_identifier(s)?;
    let (s, e) = many0(variable_dimension)(s)?;
    let (s, f) = opt(pair(symbol("="), property_actual_arg))(s)?;
    Ok((
        s,
        CheckerPortItem {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

#[trace]
pub fn checker_port_direction(s: Span) -> IResult<Span, CheckerPortDirection> {
    alt((
        map(symbol("input"), |x| CheckerPortDirection::Input(x)),
        map(symbol("output"), |x| CheckerPortDirection::Output(x)),
    ))(s)
}

#[trace]
pub fn checker_or_generate_item(s: Span) -> IResult<Span, CheckerOrGenerateItem> {
    alt((
        map(checker_or_generate_item_declaration, |x| {
            CheckerOrGenerateItem::CheckerOrGenerateItemDeclaration(x)
        }),
        map(initial_construct, |x| {
            CheckerOrGenerateItem::InitialConstruct(x)
        }),
        map(always_construct, |x| {
            CheckerOrGenerateItem::AlwaysConstruct(x)
        }),
        map(final_construct, |x| {
            CheckerOrGenerateItem::FinalConstruct(x)
        }),
        map(assertion_item, |x| CheckerOrGenerateItem::AssertionItem(x)),
        map(continuous_assign, |x| {
            CheckerOrGenerateItem::ContinuousAssign(x)
        }),
        map(checker_generate_item, |x| {
            CheckerOrGenerateItem::CheckerGenerateItem(x)
        }),
    ))(s)
}

#[trace]
pub fn checker_or_generate_item_declaration(
    s: Span,
) -> IResult<Span, CheckerOrGenerateItemDeclaration> {
    alt((
        checker_or_generate_item_declaration_data,
        map(function_declaration, |x| {
            CheckerOrGenerateItemDeclaration::FunctionDeclaration(x)
        }),
        map(checker_declaration, |x| {
            CheckerOrGenerateItemDeclaration::CheckerDeclaration(x)
        }),
        map(assertion_item_declaration, |x| {
            CheckerOrGenerateItemDeclaration::AssertionItemDeclaration(x)
        }),
        map(covergroup_declaration, |x| {
            CheckerOrGenerateItemDeclaration::CovergroupDeclaration(x)
        }),
        map(genvar_declaration, |x| {
            CheckerOrGenerateItemDeclaration::GenvarDeclaration(x)
        }),
        map(clocking_declaration, |x| {
            CheckerOrGenerateItemDeclaration::ClockingDeclaration(x)
        }),
        checker_or_generate_item_declaration_clocking,
        checker_or_generate_item_declaration_disable,
        map(symbol(";"), |x| CheckerOrGenerateItemDeclaration::Empty(x)),
    ))(s)
}

#[trace]
pub fn checker_or_generate_item_declaration_data(
    s: Span,
) -> IResult<Span, CheckerOrGenerateItemDeclaration> {
    let (s, a) = opt(rand)(s)?;
    let (s, b) = data_declaration(s)?;
    Ok((
        s,
        CheckerOrGenerateItemDeclaration::Data(CheckerOrGenerateItemDeclarationData {
            nodes: (a, b),
        }),
    ))
}

#[trace]
pub fn rand(s: Span) -> IResult<Span, Rand> {
    let (s, a) = symbol("rand")(s)?;
    Ok((s, Rand { nodes: (a,) }))
}

#[trace]
pub fn checker_or_generate_item_declaration_clocking(
    s: Span,
) -> IResult<Span, CheckerOrGenerateItemDeclaration> {
    let (s, a) = symbol("default")(s)?;
    let (s, b) = symbol("clocking")(s)?;
    let (s, c) = clocking_identifier(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        CheckerOrGenerateItemDeclaration::Clocking(CheckerOrGenerateItemDeclarationClocking {
            nodes: (a, b, c, d),
        }),
    ))
}

#[trace]
pub fn checker_or_generate_item_declaration_disable(
    s: Span,
) -> IResult<Span, CheckerOrGenerateItemDeclaration> {
    let (s, a) = symbol("default")(s)?;
    let (s, b) = symbol("disable")(s)?;
    let (s, c) = symbol("iff")(s)?;
    let (s, d) = expression_or_dist(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        CheckerOrGenerateItemDeclaration::Disable(CheckerOrGenerateItemDeclarationDisable {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[trace]
pub fn checker_generate_item(s: Span) -> IResult<Span, CheckerGenerateItem> {
    alt((
        map(loop_generate_construct, |x| {
            CheckerGenerateItem::LoopGenerateConstruct(Box::new(x))
        }),
        map(conditional_generate_construct, |x| {
            CheckerGenerateItem::ConditionalGenerateConstruct(Box::new(x))
        }),
        map(generate_region, |x| CheckerGenerateItem::GenerateRegion(x)),
        map(elaboration_system_task, |x| {
            CheckerGenerateItem::ElaborationSystemTask(x)
        }),
    ))(s)
}
