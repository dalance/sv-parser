use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn udp_body(s: Span) -> IResult<Span, UdpBody> {
    alt((
        map(combinational_body, |x| {
            UdpBody::CombinationalBody(Box::new(x))
        }),
        map(sequential_body, |x| UdpBody::SequentialBody(Box::new(x))),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn combinational_body(s: Span) -> IResult<Span, CombinationalBody> {
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn combinational_entry(s: Span) -> IResult<Span, CombinationalEntry> {
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn sequential_body(s: Span) -> IResult<Span, SequentialBody> {
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn udp_initial_statement(s: Span) -> IResult<Span, UdpInitialStatement> {
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn init_val(s: Span) -> IResult<Span, InitVal> {
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn sequential_entry(s: Span) -> IResult<Span, SequentialEntry> {
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn seq_input_list(s: Span) -> IResult<Span, SeqInputList> {
    alt((
        map(edge_input_list, |x| {
            SeqInputList::EdgeInputList(Box::new(x))
        }),
        map(level_input_list, |x| {
            SeqInputList::LevelInputList(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn level_input_list(s: Span) -> IResult<Span, LevelInputList> {
    let (s, a) = level_symbol(s)?;
    let (s, b) = many0(level_symbol)(s)?;
    Ok((s, LevelInputList { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn edge_input_list(s: Span) -> IResult<Span, EdgeInputList> {
    let (s, a) = many0(level_symbol)(s)?;
    let (s, b) = edge_indicator(s)?;
    let (s, c) = many0(level_symbol)(s)?;
    Ok((s, EdgeInputList { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn edge_indicator(s: Span) -> IResult<Span, EdgeIndicator> {
    alt((
        edge_indicator_paren,
        map(edge_symbol, |x| EdgeIndicator::EdgeSymbol(Box::new(x))),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn edge_indicator_paren(s: Span) -> IResult<Span, EdgeIndicator> {
    let (s, a) = paren(pair(level_symbol, level_symbol))(s)?;
    Ok((
        s,
        EdgeIndicator::Paren(Box::new(EdgeIndicatorParen { nodes: (a,) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn current_state(s: Span) -> IResult<Span, CurrentState> {
    let (s, a) = level_symbol(s)?;
    Ok((s, CurrentState { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn next_state(s: Span) -> IResult<Span, NextState> {
    alt((
        map(output_symbol, |x| NextState::OutputSymbol(Box::new(x))),
        map(symbol("-"), |x| NextState::Minus(Box::new(x))),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn output_symbol(s: Span) -> IResult<Span, OutputSymbol> {
    alt((
        map(symbol("0"), |x| OutputSymbol { nodes: (x,) }),
        map(symbol("1"), |x| OutputSymbol { nodes: (x,) }),
        map(symbol("x"), |x| OutputSymbol { nodes: (x,) }),
        map(symbol("X"), |x| OutputSymbol { nodes: (x,) }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn level_symbol(s: Span) -> IResult<Span, LevelSymbol> {
    alt((
        map(symbol("0"), |x| LevelSymbol { nodes: (x,) }),
        map(symbol("1"), |x| LevelSymbol { nodes: (x,) }),
        map(symbol("x"), |x| LevelSymbol { nodes: (x,) }),
        map(symbol("X"), |x| LevelSymbol { nodes: (x,) }),
        map(symbol("?"), |x| LevelSymbol { nodes: (x,) }),
        map(symbol("b"), |x| LevelSymbol { nodes: (x,) }),
        map(symbol("B"), |x| LevelSymbol { nodes: (x,) }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn edge_symbol(s: Span) -> IResult<Span, EdgeSymbol> {
    alt((
        map(symbol("r"), |x| EdgeSymbol { nodes: (x,) }),
        map(symbol("R"), |x| EdgeSymbol { nodes: (x,) }),
        map(symbol("f"), |x| EdgeSymbol { nodes: (x,) }),
        map(symbol("F"), |x| EdgeSymbol { nodes: (x,) }),
        map(symbol("p"), |x| EdgeSymbol { nodes: (x,) }),
        map(symbol("P"), |x| EdgeSymbol { nodes: (x,) }),
        map(symbol("n"), |x| EdgeSymbol { nodes: (x,) }),
        map(symbol("N"), |x| EdgeSymbol { nodes: (x,) }),
        map(symbol("*"), |x| EdgeSymbol { nodes: (x,) }),
    ))(s)
}
