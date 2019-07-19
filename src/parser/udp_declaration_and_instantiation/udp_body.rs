use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum UdpBody<'a> {
    CombinationalBody(CombinationalBody<'a>),
    SequentialBody(SequentialBody<'a>),
}

#[derive(Debug, Node)]
pub struct CombinationalBody<'a> {
    pub nodes: (
        Symbol<'a>,
        CombinationalEntry<'a>,
        Vec<CombinationalEntry<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct CombinationalEntry<'a> {
    pub nodes: (LevelInputList<'a>, Symbol<'a>, OutputSymbol<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct SequentialBody<'a> {
    pub nodes: (
        Option<UdpInitialStatement<'a>>,
        Symbol<'a>,
        SequentialEntry<'a>,
        Vec<SequentialEntry<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct UdpInitialStatement<'a> {
    pub nodes: (
        Symbol<'a>,
        OutputPortIdentifier<'a>,
        Symbol<'a>,
        InitVal<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct InitVal<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub struct SequentialEntry<'a> {
    pub nodes: (
        SeqInputList<'a>,
        Symbol<'a>,
        CurrentState<'a>,
        Symbol<'a>,
        NextState<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum SeqInputList<'a> {
    LevelInputList(LevelInputList<'a>),
    EdgeInputList(EdgeInputList<'a>),
}

#[derive(Debug, Node)]
pub struct LevelInputList<'a> {
    pub nodes: (LevelSymbol<'a>, Vec<LevelSymbol<'a>>),
}

#[derive(Debug, Node)]
pub struct EdgeInputList<'a> {
    pub nodes: (
        Vec<LevelSymbol<'a>>,
        EdgeIndicator<'a>,
        Vec<LevelSymbol<'a>>,
    ),
}

#[derive(Debug, Node)]
pub enum EdgeIndicator<'a> {
    Paren(EdgeIndicatorParen<'a>),
    EdgeSymbol(EdgeSymbol<'a>),
}

#[derive(Debug, Node)]
pub struct EdgeIndicatorParen<'a> {
    pub nodes: (Paren<'a, (LevelSymbol<'a>, LevelSymbol<'a>)>,),
}

#[derive(Debug, Node)]
pub struct CurrentState<'a> {
    pub nodes: (LevelSymbol<'a>,),
}

#[derive(Debug, Node)]
pub enum NextState<'a> {
    OutputSymbol(OutputSymbol<'a>),
    Minus(Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct OutputSymbol<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub struct LevelSymbol<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub struct EdgeSymbol<'a> {
    pub nodes: (Symbol<'a>,),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn udp_body(s: Span) -> IResult<Span, UdpBody> {
    alt((
        map(combinational_body, |x| UdpBody::CombinationalBody(x)),
        map(sequential_body, |x| UdpBody::SequentialBody(x)),
    ))(s)
}

#[parser]
pub fn combinational_body(s: Span) -> IResult<Span, CombinationalBody> {
    let (s, a) = keyword("table")(s)?;
    let (s, b) = combinational_entry(s)?;
    let (s, c) = many0(combinational_entry)(s)?;
    let (s, d) = keyword("endtable")(s)?;
    Ok((
        s,
        CombinationalBody {
            nodes: (a, b, c, d),
        },
    ))
}

#[parser]
pub fn combinational_entry(s: Span) -> IResult<Span, CombinationalEntry> {
    let (s, a) = level_input_list(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = output_symbol(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        CombinationalEntry {
            nodes: (a, b, c, d),
        },
    ))
}

#[parser]
pub fn sequential_body(s: Span) -> IResult<Span, SequentialBody> {
    let (s, a) = opt(udp_initial_statement)(s)?;
    let (s, b) = keyword("table")(s)?;
    let (s, c) = sequential_entry(s)?;
    let (s, d) = many0(sequential_entry)(s)?;
    let (s, e) = keyword("endtable")(s)?;
    Ok((
        s,
        SequentialBody {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser]
pub fn udp_initial_statement(s: Span) -> IResult<Span, UdpInitialStatement> {
    let (s, a) = keyword("initial")(s)?;
    let (s, b) = output_port_identifier(s)?;
    let (s, c) = symbol("=")(s)?;
    let (s, d) = init_val(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        UdpInitialStatement {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser]
pub fn init_val(s: Span) -> IResult<Span, InitVal> {
    alt((
        map(keyword("1'b0"), |x| InitVal { nodes: (x,) }),
        map(keyword("1'b1"), |x| InitVal { nodes: (x,) }),
        map(keyword("1'bx"), |x| InitVal { nodes: (x,) }),
        map(keyword("1'bX"), |x| InitVal { nodes: (x,) }),
        map(keyword("1'B0"), |x| InitVal { nodes: (x,) }),
        map(keyword("1'B1"), |x| InitVal { nodes: (x,) }),
        map(keyword("1'Bx"), |x| InitVal { nodes: (x,) }),
        map(keyword("1'BX"), |x| InitVal { nodes: (x,) }),
        map(keyword("1"), |x| InitVal { nodes: (x,) }),
        map(keyword("0"), |x| InitVal { nodes: (x,) }),
    ))(s)
}

#[parser]
pub fn sequential_entry(s: Span) -> IResult<Span, SequentialEntry> {
    let (s, a) = seq_input_list(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = current_state(s)?;
    let (s, d) = symbol(":")(s)?;
    let (s, e) = next_state(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        SequentialEntry {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

#[parser]
pub fn seq_input_list(s: Span) -> IResult<Span, SeqInputList> {
    alt((
        map(level_input_list, |x| SeqInputList::LevelInputList(x)),
        map(edge_input_list, |x| SeqInputList::EdgeInputList(x)),
    ))(s)
}

#[parser]
pub fn level_input_list(s: Span) -> IResult<Span, LevelInputList> {
    let (s, a) = level_symbol(s)?;
    let (s, b) = many0(level_symbol)(s)?;
    Ok((s, LevelInputList { nodes: (a, b) }))
}

#[parser]
pub fn edge_input_list(s: Span) -> IResult<Span, EdgeInputList> {
    let (s, a) = many0(level_symbol)(s)?;
    let (s, b) = edge_indicator(s)?;
    let (s, c) = many0(level_symbol)(s)?;
    Ok((s, EdgeInputList { nodes: (a, b, c) }))
}

#[parser]
pub fn edge_indicator(s: Span) -> IResult<Span, EdgeIndicator> {
    alt((
        edge_indicator_paren,
        map(edge_symbol, |x| EdgeIndicator::EdgeSymbol(x)),
    ))(s)
}

#[parser]
pub fn edge_indicator_paren(s: Span) -> IResult<Span, EdgeIndicator> {
    let (s, a) = paren(pair(level_symbol, level_symbol))(s)?;
    Ok((s, EdgeIndicator::Paren(EdgeIndicatorParen { nodes: (a,) })))
}

#[parser]
pub fn current_state(s: Span) -> IResult<Span, CurrentState> {
    let (s, a) = level_symbol(s)?;
    Ok((s, CurrentState { nodes: (a,) }))
}

#[parser]
pub fn next_state(s: Span) -> IResult<Span, NextState> {
    alt((
        map(output_symbol, |x| NextState::OutputSymbol(x)),
        map(symbol("-"), |x| NextState::Minus(x)),
    ))(s)
}

#[parser]
pub fn output_symbol(s: Span) -> IResult<Span, OutputSymbol> {
    alt((
        map(keyword("0"), |x| OutputSymbol { nodes: (x,) }),
        map(keyword("1"), |x| OutputSymbol { nodes: (x,) }),
        map(keyword("x"), |x| OutputSymbol { nodes: (x,) }),
        map(keyword("X"), |x| OutputSymbol { nodes: (x,) }),
    ))(s)
}

#[parser]
pub fn level_symbol(s: Span) -> IResult<Span, LevelSymbol> {
    alt((
        map(keyword("0"), |x| LevelSymbol { nodes: (x,) }),
        map(keyword("1"), |x| LevelSymbol { nodes: (x,) }),
        map(keyword("x"), |x| LevelSymbol { nodes: (x,) }),
        map(keyword("X"), |x| LevelSymbol { nodes: (x,) }),
        map(keyword("?"), |x| LevelSymbol { nodes: (x,) }),
        map(keyword("b"), |x| LevelSymbol { nodes: (x,) }),
        map(keyword("B"), |x| LevelSymbol { nodes: (x,) }),
    ))(s)
}

#[parser]
pub fn edge_symbol(s: Span) -> IResult<Span, EdgeSymbol> {
    alt((
        map(keyword("r"), |x| EdgeSymbol { nodes: (x,) }),
        map(keyword("R"), |x| EdgeSymbol { nodes: (x,) }),
        map(keyword("f"), |x| EdgeSymbol { nodes: (x,) }),
        map(keyword("F"), |x| EdgeSymbol { nodes: (x,) }),
        map(keyword("p"), |x| EdgeSymbol { nodes: (x,) }),
        map(keyword("P"), |x| EdgeSymbol { nodes: (x,) }),
        map(keyword("n"), |x| EdgeSymbol { nodes: (x,) }),
        map(keyword("N"), |x| EdgeSymbol { nodes: (x,) }),
        map(keyword("*"), |x| EdgeSymbol { nodes: (x,) }),
    ))(s)
}
