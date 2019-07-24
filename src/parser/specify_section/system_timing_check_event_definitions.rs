use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct TimingCheckEvent {
    pub nodes: (
        Option<TimingCheckEventControl>,
        SpecifyTerminalDescriptor,
        Option<(Symbol, TimingCheckCondition)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ControlledTimingCheckEvent {
    pub nodes: (
        TimingCheckEventControl,
        SpecifyTerminalDescriptor,
        Option<(Symbol, TimingCheckCondition)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum TimingCheckEventControl {
    Posedge(Keyword),
    Negedge(Keyword),
    Edge(Keyword),
    EdgeControlSpecifier(EdgeControlSpecifier),
}

#[derive(Clone, Debug, Node)]
pub enum SpecifyTerminalDescriptor {
    SpecifyInputTerminalDescriptor(SpecifyInputTerminalDescriptor),
    SpecifyOutputTerminalDescriptor(SpecifyOutputTerminalDescriptor),
}

#[derive(Clone, Debug, Node)]
pub struct EdgeControlSpecifier {
    pub nodes: (Keyword, Bracket<List<Symbol, EdgeDescriptor>>),
}

#[derive(Clone, Debug, Node)]
pub struct EdgeDescriptor {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, Node)]
pub enum TimingCheckCondition {
    ScalarTimingCheckCondition(ScalarTimingCheckCondition),
    Paren(TimingCheckConditionParen),
}

#[derive(Clone, Debug, Node)]
pub struct TimingCheckConditionParen {
    pub nodes: (Paren<ScalarTimingCheckCondition>,),
}

#[derive(Clone, Debug, Node)]
pub enum ScalarTimingCheckCondition {
    Expression(Expression),
    Unary(ScalarTimingCheckConditionUnary),
    Binary(ScalarTimingCheckConditionBinary),
}

#[derive(Clone, Debug, Node)]
pub struct ScalarTimingCheckConditionUnary {
    pub nodes: (Symbol, Expression),
}

#[derive(Clone, Debug, Node)]
pub struct ScalarTimingCheckConditionBinary {
    pub nodes: (Expression, Symbol, ScalarConstant),
}

#[derive(Clone, Debug, Node)]
pub struct ScalarConstant {
    pub nodes: (Keyword,),
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
        map(keyword("posedge"), |x| TimingCheckEventControl::Posedge(x)),
        map(keyword("negedge"), |x| TimingCheckEventControl::Negedge(x)),
        map(keyword("edge"), |x| TimingCheckEventControl::Edge(x)),
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
    let (s, a) = keyword("edge")(s)?;
    let (s, b) = bracket(list(symbol(","), edge_descriptor))(s)?;
    Ok((s, EdgeControlSpecifier { nodes: (a, b) }))
}

#[parser]
pub fn edge_descriptor(s: Span) -> IResult<Span, EdgeDescriptor> {
    alt((
        map(keyword("01"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("10"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("x0"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("x1"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("X0"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("X1"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("z0"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("z1"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("Z0"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("Z1"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("0x"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("1x"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("0X"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("1X"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("0z"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("1z"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("0Z"), |x| EdgeDescriptor { nodes: (x,) }),
        map(keyword("1Z"), |x| EdgeDescriptor { nodes: (x,) }),
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
        map(keyword("1'b0"), |x| ScalarConstant { nodes: (x,) }),
        map(keyword("1'b1"), |x| ScalarConstant { nodes: (x,) }),
        map(keyword("1'B0"), |x| ScalarConstant { nodes: (x,) }),
        map(keyword("1'B1"), |x| ScalarConstant { nodes: (x,) }),
        map(keyword("'b0"), |x| ScalarConstant { nodes: (x,) }),
        map(keyword("'b1"), |x| ScalarConstant { nodes: (x,) }),
        map(keyword("'B0"), |x| ScalarConstant { nodes: (x,) }),
        map(keyword("'B1"), |x| ScalarConstant { nodes: (x,) }),
        map(keyword("1"), |x| ScalarConstant { nodes: (x,) }),
        map(keyword("0"), |x| ScalarConstant { nodes: (x,) }),
    ))(s)
}
