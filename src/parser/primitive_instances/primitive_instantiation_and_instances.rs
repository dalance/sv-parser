use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum GateInstantiation {
    Cmos(Box<GateInstantiationCmos>),
    Enable(Box<GateInstantiationEnable>),
    Mos(Box<GateInstantiationMos>),
    NInput(Box<GateInstantiationNInput>),
    NOutput(Box<GateInstantiationNOutput>),
    PassEn(Box<GateInstantiationPassEn>),
    Pass(Box<GateInstantiationPass>),
    Pulldown(Box<GateInstantiationPulldown>),
    Pullup(Box<GateInstantiationPullup>),
}

#[derive(Clone, Debug, Node)]
pub struct GateInstantiationCmos {
    pub nodes: (
        CmosSwitchtype,
        Option<Delay3>,
        List<Symbol, CmosSwitchInstance>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct GateInstantiationEnable {
    pub nodes: (
        EnableGatetype,
        Option<DriveStrength>,
        Option<Delay3>,
        List<Symbol, EnableGateInstance>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct GateInstantiationMos {
    pub nodes: (
        MosSwitchtype,
        Option<Delay3>,
        List<Symbol, MosSwitchInstance>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct GateInstantiationNInput {
    pub nodes: (
        NInputGatetype,
        Option<DriveStrength>,
        Option<Delay2>,
        List<Symbol, NInputGateInstance>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct GateInstantiationNOutput {
    pub nodes: (
        NOutputGatetype,
        Option<DriveStrength>,
        Option<Delay2>,
        List<Symbol, NOutputGateInstance>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct GateInstantiationPassEn {
    pub nodes: (
        PassEnSwitchtype,
        Option<Delay2>,
        List<Symbol, PassEnableSwitchInstance>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct GateInstantiationPass {
    pub nodes: (PassSwitchtype, List<Symbol, PassSwitchInstance>, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct GateInstantiationPulldown {
    pub nodes: (
        Keyword,
        Option<PulldownStrength>,
        List<Symbol, PullGateInstance>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct GateInstantiationPullup {
    pub nodes: (
        Keyword,
        Option<PullupStrength>,
        List<Symbol, PullGateInstance>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct CmosSwitchInstance {
    pub nodes: (
        Option<NameOfInstance>,
        Paren<(
            OutputTerminal,
            Symbol,
            InputTerminal,
            Symbol,
            NcontrolTerminal,
            Symbol,
            PcontrolTerminal,
        )>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct EnableGateInstance {
    pub nodes: (
        Option<NameOfInstance>,
        Paren<(
            OutputTerminal,
            Symbol,
            InputTerminal,
            Symbol,
            EnableTerminal,
        )>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct MosSwitchInstance {
    pub nodes: (
        Option<NameOfInstance>,
        Paren<(
            OutputTerminal,
            Symbol,
            InputTerminal,
            Symbol,
            EnableTerminal,
        )>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct NInputGateInstance {
    pub nodes: (
        Option<NameOfInstance>,
        Paren<(OutputTerminal, Symbol, List<Symbol, InputTerminal>)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct NOutputGateInstance {
    pub nodes: (
        Option<NameOfInstance>,
        Paren<(List<Symbol, OutputTerminal>, Symbol, InputTerminal)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct PassSwitchInstance {
    pub nodes: (
        Option<NameOfInstance>,
        Paren<(InoutTerminal, Symbol, InoutTerminal)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct PassEnableSwitchInstance {
    pub nodes: (
        Option<NameOfInstance>,
        Paren<(InoutTerminal, Symbol, InoutTerminal, Symbol, EnableTerminal)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct PullGateInstance {
    pub nodes: (Option<NameOfInstance>, Paren<OutputTerminal>),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn gate_instantiation(s: Span) -> IResult<Span, GateInstantiation> {
    alt((
        gate_instantiation_cmos,
        gate_instantiation_enable,
        gate_instantiation_mos,
        gate_instantiation_n_input,
        gate_instantiation_n_output,
        gate_instantiation_pass_en,
        gate_instantiation_pass,
        gate_instantiation_pulldown,
        gate_instantiation_pullup,
    ))(s)
}

#[parser]
pub fn gate_instantiation_cmos(s: Span) -> IResult<Span, GateInstantiation> {
    let (s, a) = cmos_switchtype(s)?;
    let (s, b) = opt(delay3)(s)?;
    let (s, c) = list(symbol(","), cmos_switch_instance)(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        GateInstantiation::Cmos(Box::new(GateInstantiationCmos {
            nodes: (a, b, c, d),
        })),
    ))
}

#[parser]
pub fn gate_instantiation_enable(s: Span) -> IResult<Span, GateInstantiation> {
    let (s, a) = enable_gatetype(s)?;
    let (s, b) = opt(drive_strength)(s)?;
    let (s, c) = opt(delay3)(s)?;
    let (s, d) = list(symbol(","), enable_gate_instance)(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        GateInstantiation::Enable(Box::new(GateInstantiationEnable {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[parser]
pub fn gate_instantiation_mos(s: Span) -> IResult<Span, GateInstantiation> {
    let (s, a) = mos_switchtype(s)?;
    let (s, b) = opt(delay3)(s)?;
    let (s, c) = list(symbol(","), mos_switch_instance)(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        GateInstantiation::Mos(Box::new(GateInstantiationMos {
            nodes: (a, b, c, d),
        })),
    ))
}

#[parser]
pub fn gate_instantiation_n_input(s: Span) -> IResult<Span, GateInstantiation> {
    let (s, a) = n_input_gatetype(s)?;
    let (s, b) = opt(drive_strength)(s)?;
    let (s, c) = opt(delay2)(s)?;
    let (s, d) = list(symbol(","), n_input_gate_instance)(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        GateInstantiation::NInput(Box::new(GateInstantiationNInput {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[parser]
pub fn gate_instantiation_n_output(s: Span) -> IResult<Span, GateInstantiation> {
    let (s, a) = n_output_gatetype(s)?;
    let (s, b) = opt(drive_strength)(s)?;
    let (s, c) = opt(delay2)(s)?;
    let (s, d) = list(symbol(","), n_output_gate_instance)(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        GateInstantiation::NOutput(Box::new(GateInstantiationNOutput {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[parser]
pub fn gate_instantiation_pass_en(s: Span) -> IResult<Span, GateInstantiation> {
    let (s, a) = pass_en_switchtype(s)?;
    let (s, b) = opt(delay2)(s)?;
    let (s, c) = list(symbol(","), pass_enable_switch_instance)(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        GateInstantiation::PassEn(Box::new(GateInstantiationPassEn {
            nodes: (a, b, c, d),
        })),
    ))
}

#[parser]
pub fn gate_instantiation_pass(s: Span) -> IResult<Span, GateInstantiation> {
    let (s, a) = pass_switchtype(s)?;
    let (s, b) = list(symbol(","), pass_switch_instance)(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        GateInstantiation::Pass(Box::new(GateInstantiationPass { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn gate_instantiation_pulldown(s: Span) -> IResult<Span, GateInstantiation> {
    let (s, a) = keyword("pulldown")(s)?;
    let (s, b) = opt(pulldown_strength)(s)?;
    let (s, c) = list(symbol(","), pull_gate_instance)(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        GateInstantiation::Pulldown(Box::new(GateInstantiationPulldown {
            nodes: (a, b, c, d),
        })),
    ))
}

#[parser]
pub fn gate_instantiation_pullup(s: Span) -> IResult<Span, GateInstantiation> {
    let (s, a) = keyword("pullup")(s)?;
    let (s, b) = opt(pullup_strength)(s)?;
    let (s, c) = list(symbol(","), pull_gate_instance)(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        GateInstantiation::Pullup(Box::new(GateInstantiationPullup {
            nodes: (a, b, c, d),
        })),
    ))
}

#[parser]
pub fn cmos_switch_instance(s: Span) -> IResult<Span, CmosSwitchInstance> {
    let (s, a) = opt(name_of_instance)(s)?;
    let (s, b) = paren(tuple((
        output_terminal,
        symbol(","),
        input_terminal,
        symbol(","),
        ncontrol_terminal,
        symbol(","),
        pcontrol_terminal,
    )))(s)?;
    Ok((s, CmosSwitchInstance { nodes: (a, b) }))
}

#[parser]
pub fn enable_gate_instance(s: Span) -> IResult<Span, EnableGateInstance> {
    let (s, a) = opt(name_of_instance)(s)?;
    let (s, b) = paren(tuple((
        output_terminal,
        symbol(","),
        input_terminal,
        symbol(","),
        enable_terminal,
    )))(s)?;
    Ok((s, EnableGateInstance { nodes: (a, b) }))
}

#[parser]
pub fn mos_switch_instance(s: Span) -> IResult<Span, MosSwitchInstance> {
    let (s, a) = opt(name_of_instance)(s)?;
    let (s, b) = paren(tuple((
        output_terminal,
        symbol(","),
        input_terminal,
        symbol(","),
        enable_terminal,
    )))(s)?;
    Ok((s, MosSwitchInstance { nodes: (a, b) }))
}

#[parser]
pub fn n_input_gate_instance(s: Span) -> IResult<Span, NInputGateInstance> {
    let (s, a) = opt(name_of_instance)(s)?;
    let (s, b) = paren(tuple((
        output_terminal,
        symbol(","),
        list(symbol(","), input_terminal),
    )))(s)?;
    Ok((s, NInputGateInstance { nodes: (a, b) }))
}

#[parser]
pub fn n_output_gate_instance(s: Span) -> IResult<Span, NOutputGateInstance> {
    let (s, a) = opt(name_of_instance)(s)?;
    let (s, b) = paren(tuple((
        list(symbol(","), output_terminal),
        symbol(","),
        input_terminal,
    )))(s)?;
    Ok((s, NOutputGateInstance { nodes: (a, b) }))
}

#[parser]
pub fn pass_switch_instance(s: Span) -> IResult<Span, PassSwitchInstance> {
    let (s, a) = opt(name_of_instance)(s)?;
    let (s, b) = paren(tuple((inout_terminal, symbol(","), inout_terminal)))(s)?;
    Ok((s, PassSwitchInstance { nodes: (a, b) }))
}

#[parser]
pub fn pass_enable_switch_instance(s: Span) -> IResult<Span, PassEnableSwitchInstance> {
    let (s, a) = opt(name_of_instance)(s)?;
    let (s, b) = paren(tuple((
        inout_terminal,
        symbol(","),
        inout_terminal,
        symbol(","),
        enable_terminal,
    )))(s)?;
    Ok((s, PassEnableSwitchInstance { nodes: (a, b) }))
}

#[parser]
pub fn pull_gate_instance(s: Span) -> IResult<Span, PullGateInstance> {
    let (s, a) = opt(name_of_instance)(s)?;
    let (s, b) = paren(output_terminal)(s)?;
    Ok((s, PullGateInstance { nodes: (a, b) }))
}
