use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct CheckerPortList {
    pub nodes: (List<Symbol, CheckerPortItem>,),
}

#[derive(Clone, Debug, Node)]
pub struct CheckerPortItem {
    pub nodes: (
        Vec<AttributeInstance>,
        Option<CheckerPortDirection>,
        PropertyFormalType,
        FormalPortIdentifier,
        Vec<VariableDimension>,
        Option<(Symbol, PropertyActualArg)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum CheckerPortDirection {
    Input(Box<Keyword>),
    Output(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub enum CheckerOrGenerateItem {
    CheckerOrGenerateItemDeclaration(Box<CheckerOrGenerateItemDeclaration>),
    InitialConstruct(Box<InitialConstruct>),
    AlwaysConstruct(Box<AlwaysConstruct>),
    FinalConstruct(Box<FinalConstruct>),
    AssertionItem(Box<AssertionItem>),
    ContinuousAssign(Box<ContinuousAssign>),
    CheckerGenerateItem(Box<CheckerGenerateItem>),
}

#[derive(Clone, Debug, Node)]
pub enum CheckerOrGenerateItemDeclaration {
    Data(Box<CheckerOrGenerateItemDeclarationData>),
    FunctionDeclaration(Box<FunctionDeclaration>),
    CheckerDeclaration(Box<CheckerDeclaration>),
    AssertionItemDeclaration(Box<AssertionItemDeclaration>),
    CovergroupDeclaration(Box<CovergroupDeclaration>),
    GenvarDeclaration(Box<GenvarDeclaration>),
    ClockingDeclaration(Box<ClockingDeclaration>),
    Clocking(Box<CheckerOrGenerateItemDeclarationClocking>),
    Disable(Box<CheckerOrGenerateItemDeclarationDisable>),
    Empty(Box<Symbol>),
}

#[derive(Clone, Debug, Node)]
pub struct CheckerOrGenerateItemDeclarationData {
    pub nodes: (Option<Rand>, DataDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct Rand {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, Node)]
pub struct CheckerOrGenerateItemDeclarationClocking {
    pub nodes: (Keyword, Keyword, ClockingIdentifier, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct CheckerOrGenerateItemDeclarationDisable {
    pub nodes: (Keyword, Keyword, Keyword, ExpressionOrDist, Symbol),
}

#[derive(Clone, Debug, Node)]
pub enum CheckerGenerateItem {
    LoopGenerateConstruct(Box<LoopGenerateConstruct>),
    ConditionalGenerateConstruct(Box<ConditionalGenerateConstruct>),
    GenerateRegion(Box<GenerateRegion>),
    ElaborationSystemTask(Box<ElaborationSystemTask>),
}

// -----------------------------------------------------------------------------

#[parser]
pub(crate) fn checker_port_list(s: Span) -> IResult<Span, CheckerPortList> {
    let (s, a) = list(symbol(","), checker_port_item)(s)?;
    Ok((s, CheckerPortList { nodes: (a,) }))
}

#[parser]
pub(crate) fn checker_port_item(s: Span) -> IResult<Span, CheckerPortItem> {
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

#[parser]
pub(crate) fn checker_port_direction(s: Span) -> IResult<Span, CheckerPortDirection> {
    alt((
        map(keyword("input"), |x| {
            CheckerPortDirection::Input(Box::new(x))
        }),
        map(keyword("output"), |x| {
            CheckerPortDirection::Output(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn checker_or_generate_item(s: Span) -> IResult<Span, CheckerOrGenerateItem> {
    alt((
        map(checker_or_generate_item_declaration, |x| {
            CheckerOrGenerateItem::CheckerOrGenerateItemDeclaration(Box::new(x))
        }),
        map(initial_construct, |x| {
            CheckerOrGenerateItem::InitialConstruct(Box::new(x))
        }),
        map(always_construct, |x| {
            CheckerOrGenerateItem::AlwaysConstruct(Box::new(x))
        }),
        map(final_construct, |x| {
            CheckerOrGenerateItem::FinalConstruct(Box::new(x))
        }),
        map(assertion_item, |x| {
            CheckerOrGenerateItem::AssertionItem(Box::new(x))
        }),
        map(continuous_assign, |x| {
            CheckerOrGenerateItem::ContinuousAssign(Box::new(x))
        }),
        map(checker_generate_item, |x| {
            CheckerOrGenerateItem::CheckerGenerateItem(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn checker_or_generate_item_declaration(
    s: Span,
) -> IResult<Span, CheckerOrGenerateItemDeclaration> {
    alt((
        checker_or_generate_item_declaration_data,
        map(function_declaration, |x| {
            CheckerOrGenerateItemDeclaration::FunctionDeclaration(Box::new(x))
        }),
        map(checker_declaration, |x| {
            CheckerOrGenerateItemDeclaration::CheckerDeclaration(Box::new(x))
        }),
        map(assertion_item_declaration, |x| {
            CheckerOrGenerateItemDeclaration::AssertionItemDeclaration(Box::new(x))
        }),
        map(covergroup_declaration, |x| {
            CheckerOrGenerateItemDeclaration::CovergroupDeclaration(Box::new(x))
        }),
        map(genvar_declaration, |x| {
            CheckerOrGenerateItemDeclaration::GenvarDeclaration(Box::new(x))
        }),
        map(clocking_declaration, |x| {
            CheckerOrGenerateItemDeclaration::ClockingDeclaration(Box::new(x))
        }),
        checker_or_generate_item_declaration_clocking,
        checker_or_generate_item_declaration_disable,
        map(symbol(";"), |x| {
            CheckerOrGenerateItemDeclaration::Empty(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn checker_or_generate_item_declaration_data(
    s: Span,
) -> IResult<Span, CheckerOrGenerateItemDeclaration> {
    let (s, a) = opt(rand)(s)?;
    let (s, b) = data_declaration(s)?;
    Ok((
        s,
        CheckerOrGenerateItemDeclaration::Data(Box::new(CheckerOrGenerateItemDeclarationData {
            nodes: (a, b),
        })),
    ))
}

#[parser]
pub(crate) fn rand(s: Span) -> IResult<Span, Rand> {
    let (s, a) = keyword("rand")(s)?;
    Ok((s, Rand { nodes: (a,) }))
}

#[parser]
pub(crate) fn checker_or_generate_item_declaration_clocking(
    s: Span,
) -> IResult<Span, CheckerOrGenerateItemDeclaration> {
    let (s, a) = keyword("default")(s)?;
    let (s, b) = keyword("clocking")(s)?;
    let (s, c) = clocking_identifier(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        CheckerOrGenerateItemDeclaration::Clocking(Box::new(
            CheckerOrGenerateItemDeclarationClocking {
                nodes: (a, b, c, d),
            },
        )),
    ))
}

#[parser]
pub(crate) fn checker_or_generate_item_declaration_disable(
    s: Span,
) -> IResult<Span, CheckerOrGenerateItemDeclaration> {
    let (s, a) = keyword("default")(s)?;
    let (s, b) = keyword("disable")(s)?;
    let (s, c) = keyword("iff")(s)?;
    let (s, d) = expression_or_dist(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        CheckerOrGenerateItemDeclaration::Disable(Box::new(
            CheckerOrGenerateItemDeclarationDisable {
                nodes: (a, b, c, d, e),
            },
        )),
    ))
}

#[parser]
pub(crate) fn checker_generate_item(s: Span) -> IResult<Span, CheckerGenerateItem> {
    alt((
        map(loop_generate_construct, |x| {
            CheckerGenerateItem::LoopGenerateConstruct(Box::new(x))
        }),
        map(conditional_generate_construct, |x| {
            CheckerGenerateItem::ConditionalGenerateConstruct(Box::new(x))
        }),
        map(generate_region, |x| {
            CheckerGenerateItem::GenerateRegion(Box::new(x))
        }),
        map(elaboration_system_task, |x| {
            CheckerGenerateItem::ElaborationSystemTask(Box::new(x))
        }),
    ))(s)
}
