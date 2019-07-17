use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum GateInstantiation<'a> {
    Cmos(GateInstantiationCmos<'a>),
    Enable(GateInstantiationEnable<'a>),
    Mos(GateInstantiationMos<'a>),
    NInput(GateInstantiationNInput<'a>),
    NOutput(GateInstantiationNOutput<'a>),
    PassEn(GateInstantiationPassEn<'a>),
    Pass(GateInstantiationPass<'a>),
    Pulldown(GateInstantiationPulldown<'a>),
    Pullup(GateInstantiationPullup<'a>),
}

#[derive(Debug, Node)]
pub struct GateInstantiationCmos<'a> {
    pub nodes: (
        CmosSwitchtype<'a>,
        Option<Delay3<'a>>,
        List<Symbol<'a>, CmosSwitchInstance<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct GateInstantiationEnable<'a> {
    pub nodes: (
        EnableGatetype<'a>,
        Option<DriveStrength<'a>>,
        Option<Delay3<'a>>,
        List<Symbol<'a>, EnableGateInstance<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct GateInstantiationMos<'a> {
    pub nodes: (
        MosSwitchtype<'a>,
        Option<Delay3<'a>>,
        List<Symbol<'a>, MosSwitchInstance<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct GateInstantiationNInput<'a> {
    pub nodes: (
        NInputGatetype<'a>,
        Option<DriveStrength<'a>>,
        Option<Delay2<'a>>,
        List<Symbol<'a>, NInputGateInstance<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct GateInstantiationNOutput<'a> {
    pub nodes: (
        NOutputGatetype<'a>,
        Option<DriveStrength<'a>>,
        Option<Delay2<'a>>,
        List<Symbol<'a>, NOutputGateInstance<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct GateInstantiationPassEn<'a> {
    pub nodes: (
        PassEnSwitchtype<'a>,
        Option<Delay2<'a>>,
        List<Symbol<'a>, PassEnableSwitchInstance<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct GateInstantiationPass<'a> {
    pub nodes: (
        PassSwitchtype<'a>,
        List<Symbol<'a>, PassSwitchInstance<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct GateInstantiationPulldown<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<PulldownStrength<'a>>,
        List<Symbol<'a>, PullGateInstance<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct GateInstantiationPullup<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<PullupStrength<'a>>,
        List<Symbol<'a>, PullGateInstance<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct CmosSwitchInstance<'a> {
    pub nodes: (
        Option<NameOfInstance<'a>>,
        Paren<
            'a,
            (
                OutputTerminal<'a>,
                Symbol<'a>,
                InputTerminal<'a>,
                Symbol<'a>,
                NcontrolTerminal<'a>,
                Symbol<'a>,
                PcontrolTerminal<'a>,
            ),
        >,
    ),
}

#[derive(Debug, Node)]
pub struct EnableGateInstance<'a> {
    pub nodes: (
        Option<NameOfInstance<'a>>,
        Paren<
            'a,
            (
                OutputTerminal<'a>,
                Symbol<'a>,
                InputTerminal<'a>,
                Symbol<'a>,
                EnableTerminal<'a>,
            ),
        >,
    ),
}

#[derive(Debug, Node)]
pub struct MosSwitchInstance<'a> {
    pub nodes: (
        Option<NameOfInstance<'a>>,
        Paren<
            'a,
            (
                OutputTerminal<'a>,
                Symbol<'a>,
                InputTerminal<'a>,
                Symbol<'a>,
                EnableTerminal<'a>,
            ),
        >,
    ),
}

#[derive(Debug, Node)]
pub struct NInputGateInstance<'a> {
    pub nodes: (
        Option<NameOfInstance<'a>>,
        Paren<
            'a,
            (
                OutputTerminal<'a>,
                Symbol<'a>,
                List<Symbol<'a>, InputTerminal<'a>>,
            ),
        >,
    ),
}

#[derive(Debug, Node)]
pub struct NOutputGateInstance<'a> {
    pub nodes: (
        Option<NameOfInstance<'a>>,
        Paren<
            'a,
            (
                List<Symbol<'a>, OutputTerminal<'a>>,
                Symbol<'a>,
                InputTerminal<'a>,
            ),
        >,
    ),
}

#[derive(Debug, Node)]
pub struct PassSwitchInstance<'a> {
    pub nodes: (
        Option<NameOfInstance<'a>>,
        Paren<'a, (InoutTerminal<'a>, Symbol<'a>, InoutTerminal<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct PassEnableSwitchInstance<'a> {
    pub nodes: (
        Option<NameOfInstance<'a>>,
        Paren<
            'a,
            (
                InoutTerminal<'a>,
                Symbol<'a>,
                InoutTerminal<'a>,
                Symbol<'a>,
                EnableTerminal<'a>,
            ),
        >,
    ),
}

#[derive(Debug, Node)]
pub struct PullGateInstance<'a> {
    pub nodes: (Option<NameOfInstance<'a>>, Paren<'a, OutputTerminal<'a>>),
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
        GateInstantiation::Cmos(GateInstantiationCmos {
            nodes: (a, b, c, d),
        }),
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
        GateInstantiation::Enable(GateInstantiationEnable {
            nodes: (a, b, c, d, e),
        }),
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
        GateInstantiation::Mos(GateInstantiationMos {
            nodes: (a, b, c, d),
        }),
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
        GateInstantiation::NInput(GateInstantiationNInput {
            nodes: (a, b, c, d, e),
        }),
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
        GateInstantiation::NOutput(GateInstantiationNOutput {
            nodes: (a, b, c, d, e),
        }),
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
        GateInstantiation::PassEn(GateInstantiationPassEn {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn gate_instantiation_pass(s: Span) -> IResult<Span, GateInstantiation> {
    let (s, a) = pass_switchtype(s)?;
    let (s, b) = list(symbol(","), pass_switch_instance)(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        GateInstantiation::Pass(GateInstantiationPass { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn gate_instantiation_pulldown(s: Span) -> IResult<Span, GateInstantiation> {
    let (s, a) = symbol("pulldown")(s)?;
    let (s, b) = opt(pulldown_strength)(s)?;
    let (s, c) = list(symbol(","), pull_gate_instance)(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        GateInstantiation::Pulldown(GateInstantiationPulldown {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn gate_instantiation_pullup(s: Span) -> IResult<Span, GateInstantiation> {
    let (s, a) = symbol("pullup")(s)?;
    let (s, b) = opt(pullup_strength)(s)?;
    let (s, c) = list(symbol(","), pull_gate_instance)(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        GateInstantiation::Pullup(GateInstantiationPullup {
            nodes: (a, b, c, d),
        }),
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
