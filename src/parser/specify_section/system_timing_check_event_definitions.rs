use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct TimingCheckEvent<'a> {
    pub nodes: (
        Option<TimingCheckEventControl<'a>>,
        SpecifyTerminalDescriptor<'a>,
        Option<(Symbol<'a>, TimingCheckCondition<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct ControlledTimingCheckEvent<'a> {
    pub nodes: (
        TimingCheckEventControl<'a>,
        SpecifyTerminalDescriptor<'a>,
        Option<(Symbol<'a>, TimingCheckCondition<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub enum TimingCheckEventControl<'a> {
    Posedge(Symbol<'a>),
    Negedge(Symbol<'a>),
    Edge(Symbol<'a>),
    EdgeControlSpecifier(EdgeControlSpecifier<'a>),
}

#[derive(Debug, Node)]
pub enum SpecifyTerminalDescriptor<'a> {
    SpecifyInputTerminalDescriptor(SpecifyInputTerminalDescriptor<'a>),
    SpecifyOutputTerminalDescriptor(SpecifyOutputTerminalDescriptor<'a>),
}

#[derive(Debug, Node)]
pub struct EdgeControlSpecifier<'a> {
    pub nodes: (
        Symbol<'a>,
        Bracket<'a, List<Symbol<'a>, EdgeDescriptor<'a>>>,
    ),
}

#[derive(Debug, Node)]
pub struct EdgeDescriptor<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub enum TimingCheckCondition<'a> {
    ScalarTimingCheckCondition(ScalarTimingCheckCondition<'a>),
    Paren(TimingCheckConditionParen<'a>),
}

#[derive(Debug, Node)]
pub struct TimingCheckConditionParen<'a> {
    pub nodes: (Paren<'a, ScalarTimingCheckCondition<'a>>,),
}

#[derive(Debug, Node)]
pub enum ScalarTimingCheckCondition<'a> {
    Expression(Expression<'a>),
    Unary(ScalarTimingCheckConditionUnary<'a>),
    Binary(ScalarTimingCheckConditionBinary<'a>),
}

#[derive(Debug, Node)]
pub struct ScalarTimingCheckConditionUnary<'a> {
    pub nodes: (Symbol<'a>, Expression<'a>),
}

#[derive(Debug, Node)]
pub struct ScalarTimingCheckConditionBinary<'a> {
    pub nodes: (Expression<'a>, Symbol<'a>, ScalarConstant<'a>),
}

#[derive(Debug, Node)]
pub struct ScalarConstant<'a> {
    pub nodes: (Symbol<'a>,),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn timing_check_event(s: Span) -> IResult<Span, TimingCheckEvent> {
    let (s, a) = opt(timing_check_event_control)(s)?;
    let (s, b) = specify_terminal_descriptor(s)?;
    let (s, c) = opt(pair(symbol("&&&"), timing_check_condition))(s)?;
    Ok((s, TimingCheckEvent { nodes: (a, b, c) }))
}

#[parser]
pub fn controlled_timing_check_event(s: Span) -> IResult<Span, ControlledTimingCheckEvent> {
    let (s, a) = timing_check_event_control(s)?;
    let (s, b) = specify_terminal_descriptor(s)?;
    let (s, c) = opt(pair(symbol("&&&"), timing_check_condition))(s)?;
    Ok((s, ControlledTimingCheckEvent { nodes: (a, b, c) }))
}

#[parser]
pub fn timing_check_event_control(s: Span) -> IResult<Span, TimingCheckEventControl> {
    alt((
        map(symbol("posedge"), |x| TimingCheckEventControl::Posedge(x)),
        map(symbol("negedge"), |x| TimingCheckEventControl::Negedge(x)),
        map(symbol("edge"), |x| TimingCheckEventControl::Edge(x)),
        map(edge_control_specifier, |x| {
            TimingCheckEventControl::EdgeControlSpecifier(x)
        }),
    ))(s)
}

#[parser]
pub fn specify_terminal_descriptor(s: Span) -> IResult<Span, SpecifyTerminalDescriptor> {
    alt((
        map(specify_input_terminal_descriptor, |x| {
            SpecifyTerminalDescriptor::SpecifyInputTerminalDescriptor(x)
        }),
        map(specify_output_terminal_descriptor, |x| {
            SpecifyTerminalDescriptor::SpecifyOutputTerminalDescriptor(x)
        }),
    ))(s)
}

#[parser]
pub fn edge_control_specifier(s: Span) -> IResult<Span, EdgeControlSpecifier> {
    let (s, a) = symbol("edge")(s)?;
    let (s, b) = bracket(list(symbol(","), edge_descriptor))(s)?;
    Ok((s, EdgeControlSpecifier { nodes: (a, b) }))
}

#[parser]
pub fn edge_descriptor(s: Span) -> IResult<Span, EdgeDescriptor> {
    alt((
        map(symbol("01"), |x| EdgeDescriptor { nodes: (x,) }),
        map(symbol("10"), |x| EdgeDescriptor { nodes: (x,) }),
        map(symbol("x0"), |x| EdgeDescriptor { nodes: (x,) }),
        map(symbol("x1"), |x| EdgeDescriptor { nodes: (x,) }),
        map(symbol("X0"), |x| EdgeDescriptor { nodes: (x,) }),
        map(symbol("X1"), |x| EdgeDescriptor { nodes: (x,) }),
        map(symbol("z0"), |x| EdgeDescriptor { nodes: (x,) }),
        map(symbol("z1"), |x| EdgeDescriptor { nodes: (x,) }),
        map(symbol("Z0"), |x| EdgeDescriptor { nodes: (x,) }),
        map(symbol("Z1"), |x| EdgeDescriptor { nodes: (x,) }),
        map(symbol("0x"), |x| EdgeDescriptor { nodes: (x,) }),
        map(symbol("1x"), |x| EdgeDescriptor { nodes: (x,) }),
        map(symbol("0X"), |x| EdgeDescriptor { nodes: (x,) }),
        map(symbol("1X"), |x| EdgeDescriptor { nodes: (x,) }),
        map(symbol("0z"), |x| EdgeDescriptor { nodes: (x,) }),
        map(symbol("1z"), |x| EdgeDescriptor { nodes: (x,) }),
        map(symbol("0Z"), |x| EdgeDescriptor { nodes: (x,) }),
        map(symbol("1Z"), |x| EdgeDescriptor { nodes: (x,) }),
    ))(s)
}

#[parser]
pub fn timing_check_condition(s: Span) -> IResult<Span, TimingCheckCondition> {
    alt((
        map(scalar_timing_check_condition, |x| {
            TimingCheckCondition::ScalarTimingCheckCondition(x)
        }),
        timing_check_condition_paren,
    ))(s)
}

#[parser]
pub fn timing_check_condition_paren(s: Span) -> IResult<Span, TimingCheckCondition> {
    let (s, a) = paren(scalar_timing_check_condition)(s)?;
    Ok((
        s,
        TimingCheckCondition::Paren(TimingCheckConditionParen { nodes: (a,) }),
    ))
}

#[parser]
pub fn scalar_timing_check_condition(s: Span) -> IResult<Span, ScalarTimingCheckCondition> {
    alt((
        map(expression, |x| ScalarTimingCheckCondition::Expression(x)),
        scalar_timing_check_condition_unary,
        scalar_timing_check_condition_binary,
    ))(s)
}

#[parser]
pub fn scalar_timing_check_condition_unary(s: Span) -> IResult<Span, ScalarTimingCheckCondition> {
    let (s, a) = symbol("~")(s)?;
    let (s, b) = expression(s)?;
    Ok((
        s,
        ScalarTimingCheckCondition::Unary(ScalarTimingCheckConditionUnary { nodes: (a, b) }),
    ))
}

#[parser]
pub fn scalar_timing_check_condition_binary(s: Span) -> IResult<Span, ScalarTimingCheckCondition> {
    let (s, a) = expression(s)?;
    let (s, b) = alt((symbol("==="), symbol("=="), symbol("!=="), symbol("!=")))(s)?;
    let (s, c) = scalar_constant(s)?;
    Ok((
        s,
        ScalarTimingCheckCondition::Binary(ScalarTimingCheckConditionBinary { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn scalar_constant(s: Span) -> IResult<Span, ScalarConstant> {
    alt((
        map(symbol("1'b0"), |x| ScalarConstant { nodes: (x,) }),
        map(symbol("1'b1"), |x| ScalarConstant { nodes: (x,) }),
        map(symbol("1'B0"), |x| ScalarConstant { nodes: (x,) }),
        map(symbol("1'B1"), |x| ScalarConstant { nodes: (x,) }),
        map(symbol("'b0"), |x| ScalarConstant { nodes: (x,) }),
        map(symbol("'b1"), |x| ScalarConstant { nodes: (x,) }),
        map(symbol("'B0"), |x| ScalarConstant { nodes: (x,) }),
        map(symbol("'B1"), |x| ScalarConstant { nodes: (x,) }),
        map(symbol("1"), |x| ScalarConstant { nodes: (x,) }),
        map(symbol("0"), |x| ScalarConstant { nodes: (x,) }),
    ))(s)
}
