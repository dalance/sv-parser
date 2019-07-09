use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum ClockingDeclaration<'a> {
    Local(ClockingDeclarationLocal<'a>),
    Global(ClockingDeclarationGlobal<'a>),
}

#[derive(Debug)]
pub struct ClockingDeclarationLocal<'a> {
    pub nodes: (
        Option<Default>,
        Option<ClockingIdentifier<'a>>,
        ClockingEvent<'a>,
        Vec<ClockingItem<'a>>,
        Option<ClockingIdentifier<'a>>,
    ),
}

#[derive(Debug)]
pub struct Default {}

#[derive(Debug)]
pub struct ClockingDeclarationGlobal<'a> {
    pub nodes: (
        Option<ClockingIdentifier<'a>>,
        ClockingEvent<'a>,
        Option<ClockingIdentifier<'a>>,
    ),
}

#[derive(Debug)]
pub enum ClockingEvent<'a> {
    Identifier(Identifier<'a>),
    Expression(EventExpression<'a>),
}

#[derive(Debug)]
pub enum ClockingItem<'a> {
    DefaultSkew(DefaultSkew<'a>),
    Direction(ClockingItemDirection<'a>),
    Assertion(ClockingItemAssertion<'a>),
}

#[derive(Debug)]
pub struct ClockingItemDirection<'a> {
    pub nodes: (ClockingDirection<'a>, Vec<ClockingDeclAssign<'a>>),
}

#[derive(Debug)]
pub struct ClockingItemAssertion<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, AssertionItemDeclaration<'a>),
}

#[derive(Debug)]
pub enum DefaultSkew<'a> {
    Input(ClockingSkew<'a>),
    Output(ClockingSkew<'a>),
    InputOutput((ClockingSkew<'a>, ClockingSkew<'a>)),
}

#[derive(Debug)]
pub enum ClockingDirection<'a> {
    Input(Option<ClockingSkew<'a>>),
    Output(Option<ClockingSkew<'a>>),
    InputOutput((Option<ClockingSkew<'a>>, Option<ClockingSkew<'a>>)),
    Inout,
}

#[derive(Debug)]
pub struct ClockingDeclAssign<'a> {
    pub nodes: (SignalIdentifier<'a>, Option<Expression<'a>>),
}

#[derive(Debug)]
pub enum ClockingSkew<'a> {
    Edge((EdgeIdentifier<'a>, Option<DelayControl<'a>>)),
    Delay(DelayControl<'a>),
}

#[derive(Debug)]
pub struct ClockingDrive<'a> {
    pub nodes: (
        (HierarchicalIdentifier<'a>, Select<'a>),
        Option<CycleDelay<'a>>,
        Expression<'a>,
    ),
}

#[derive(Debug)]
pub enum CycleDelay<'a> {
    IntegralNumber(IntegralNumber<'a>),
    Identifier(Identifier<'a>),
    Expression(Expression<'a>),
}

// -----------------------------------------------------------------------------

pub fn clocking_declaration(s: &str) -> IResult<&str, ClockingDeclaration> {
    alt((clocking_declaration_local, clocking_declaration_global))(s)
}

pub fn clocking_declaration_local(s: &str) -> IResult<&str, ClockingDeclaration> {
    let (s, x) = opt(symbol("default"))(s)?;
    let (s, _) = symbol("clocking")(s)?;
    let (s, y) = opt(clocking_identifier)(s)?;
    let (s, z) = clocking_event(s)?;
    let (s, _) = symbol(";")(s)?;
    let (s, v) = many0(clocking_item)(s)?;
    let (s, _) = symbol("endclocking")(s)?;
    let (s, w) = opt(preceded(symbol(":"), clocking_identifier))(s)?;
    Ok((
        s,
        ClockingDeclaration::Local(ClockingDeclarationLocal {
            nodes: (x.map(|_| Default {}), y, z, v, w),
        }),
    ))
}

pub fn clocking_declaration_global(s: &str) -> IResult<&str, ClockingDeclaration> {
    let (s, _) = opt(symbol("global"))(s)?;
    let (s, _) = symbol("clocking")(s)?;
    let (s, x) = opt(clocking_identifier)(s)?;
    let (s, y) = clocking_event(s)?;
    let (s, _) = symbol(";")(s)?;
    let (s, _) = symbol("endclocking")(s)?;
    let (s, z) = opt(preceded(symbol(":"), clocking_identifier))(s)?;
    Ok((
        s,
        ClockingDeclaration::Global(ClockingDeclarationGlobal { nodes: (x, y, z) }),
    ))
}

pub fn clocking_event(s: &str) -> IResult<&str, ClockingEvent> {
    alt((
        map(preceded(symbol("@"), identifier), |x| {
            ClockingEvent::Identifier(x)
        }),
        map(preceded(symbol("@"), paren(event_expression)), |x| {
            ClockingEvent::Expression(x)
        }),
    ))(s)
}

pub fn clocking_item(s: &str) -> IResult<&str, ClockingItem> {
    alt((
        clocking_item_default_skew,
        clocking_item_direction,
        clocking_item_assertion,
    ))(s)
}

pub fn clocking_item_default_skew(s: &str) -> IResult<&str, ClockingItem> {
    let (s, _) = symbol("default")(s)?;
    let (s, x) = default_skew(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, ClockingItem::DefaultSkew(x)))
}

pub fn clocking_item_direction(s: &str) -> IResult<&str, ClockingItem> {
    let (s, x) = clocking_direction(s)?;
    let (s, y) = list_of_clocking_decl_assign(s)?;
    Ok((
        s,
        ClockingItem::Direction(ClockingItemDirection { nodes: (x, y) }),
    ))
}

pub fn clocking_item_assertion(s: &str) -> IResult<&str, ClockingItem> {
    let (s, x) = many0(attribute_instance)(s)?;
    let (s, y) = assertion_item_declaration(s)?;
    Ok((
        s,
        ClockingItem::Assertion(ClockingItemAssertion { nodes: (x, y) }),
    ))
}

pub fn default_skew(s: &str) -> IResult<&str, DefaultSkew> {
    alt((
        default_skew_input,
        default_skew_output,
        default_skew_input_output,
    ))(s)
}

pub fn default_skew_input(s: &str) -> IResult<&str, DefaultSkew> {
    let (s, _) = symbol("input")(s)?;
    let (s, x) = clocking_skew(s)?;
    Ok((s, DefaultSkew::Input(x)))
}

pub fn default_skew_output(s: &str) -> IResult<&str, DefaultSkew> {
    let (s, _) = symbol("output")(s)?;
    let (s, x) = clocking_skew(s)?;
    Ok((s, DefaultSkew::Output(x)))
}

pub fn default_skew_input_output(s: &str) -> IResult<&str, DefaultSkew> {
    let (s, _) = symbol("input")(s)?;
    let (s, x) = clocking_skew(s)?;
    let (s, _) = symbol("output")(s)?;
    let (s, y) = clocking_skew(s)?;
    Ok((s, DefaultSkew::InputOutput((x, y))))
}

pub fn clocking_direction(s: &str) -> IResult<&str, ClockingDirection> {
    alt((
        clocking_direction_input,
        clocking_direction_output,
        clocking_direction_input_output,
        clocking_direction_inout,
    ))(s)
}

pub fn clocking_direction_input(s: &str) -> IResult<&str, ClockingDirection> {
    let (s, _) = symbol("input")(s)?;
    let (s, x) = opt(clocking_skew)(s)?;
    Ok((s, ClockingDirection::Input(x)))
}

pub fn clocking_direction_output(s: &str) -> IResult<&str, ClockingDirection> {
    let (s, _) = symbol("output")(s)?;
    let (s, x) = opt(clocking_skew)(s)?;
    Ok((s, ClockingDirection::Output(x)))
}

pub fn clocking_direction_input_output(s: &str) -> IResult<&str, ClockingDirection> {
    let (s, _) = symbol("input")(s)?;
    let (s, x) = opt(clocking_skew)(s)?;
    let (s, _) = symbol("output")(s)?;
    let (s, y) = opt(clocking_skew)(s)?;
    Ok((s, ClockingDirection::InputOutput((x, y))))
}

pub fn clocking_direction_inout(s: &str) -> IResult<&str, ClockingDirection> {
    let (s, _) = symbol("inout")(s)?;
    Ok((s, ClockingDirection::Inout))
}

pub fn list_of_clocking_decl_assign(s: &str) -> IResult<&str, Vec<ClockingDeclAssign>> {
    many1(clocking_decl_assign)(s)
}

pub fn clocking_decl_assign(s: &str) -> IResult<&str, ClockingDeclAssign> {
    let (s, x) = signal_identifier(s)?;
    let (s, y) = opt(preceded(symbol("="), expression))(s)?;
    Ok((s, ClockingDeclAssign { nodes: (x, y) }))
}

pub fn clocking_skew(s: &str) -> IResult<&str, ClockingSkew> {
    alt((clocking_skew_edge, clocking_skew_delay))(s)
}

pub fn clocking_skew_edge(s: &str) -> IResult<&str, ClockingSkew> {
    let (s, x) = edge_identifier(s)?;
    let (s, y) = opt(delay_control)(s)?;
    Ok((s, ClockingSkew::Edge((x, y))))
}

pub fn clocking_skew_delay(s: &str) -> IResult<&str, ClockingSkew> {
    let (s, x) = delay_control(s)?;
    Ok((s, ClockingSkew::Delay(x)))
}

pub fn clocking_drive(s: &str) -> IResult<&str, ClockingDrive> {
    let (s, x) = clockvar_expression(s)?;
    let (s, _) = symbol("=")(s)?;
    let (s, y) = opt(cycle_delay)(s)?;
    let (s, z) = expression(s)?;
    Ok((s, ClockingDrive { nodes: (x, y, z) }))
}

pub fn cycle_delay(s: &str) -> IResult<&str, CycleDelay> {
    alt((
        map(preceded(symbol("##"), integral_number), |x| {
            CycleDelay::IntegralNumber(x)
        }),
        map(preceded(symbol("##"), identifier), |x| {
            CycleDelay::Identifier(x)
        }),
        map(preceded(symbol("##"), paren(expression)), |x| {
            CycleDelay::Expression(x)
        }),
    ))(s)
}

pub fn clockvar(s: &str) -> IResult<&str, HierarchicalIdentifier> {
    hierarchical_identifier(s)
}

pub fn clockvar_expression(s: &str) -> IResult<&str, (HierarchicalIdentifier, Select)> {
    pair(clockvar, select)(s)
}

// -----------------------------------------------------------------------------
