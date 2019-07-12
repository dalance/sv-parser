use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct CmosSwitchtype<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub struct EnableGatetype<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub struct MosSwitchtype<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub struct NInputGatetype<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub struct NOutputGatetype<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub struct PassEnSwitchtype<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub struct PassSwitchtype<'a> {
    pub nodes: (Symbol<'a>,),
}

// -----------------------------------------------------------------------------

pub fn cmos_switchtype(s: Span) -> IResult<Span, CmosSwitchtype> {
    let (s, a) = alt((symbol("cmos"), symbol("rcmos")))(s)?;
    Ok((s, CmosSwitchtype { nodes: (a,) }))
}

pub fn enable_gatetype(s: Span) -> IResult<Span, EnableGatetype> {
    let (s, a) = alt((
        symbol("bufif0"),
        symbol("bufif1"),
        symbol("notif0"),
        symbol("notif1"),
    ))(s)?;
    Ok((s, EnableGatetype { nodes: (a,) }))
}

pub fn mos_switchtype(s: Span) -> IResult<Span, MosSwitchtype> {
    let (s, a) = alt((
        symbol("nmos"),
        symbol("pmos"),
        symbol("rnmos"),
        symbol("rpmos"),
    ))(s)?;
    Ok((s, MosSwitchtype { nodes: (a,) }))
}

pub fn n_input_gatetype(s: Span) -> IResult<Span, NInputGatetype> {
    let (s, a) = alt((
        symbol("and"),
        symbol("nand"),
        symbol("or"),
        symbol("nor"),
        symbol("xor"),
        symbol("xnor"),
    ))(s)?;
    Ok((s, NInputGatetype { nodes: (a,) }))
}

pub fn n_output_gatetype(s: Span) -> IResult<Span, NOutputGatetype> {
    let (s, a) = alt((symbol("buf"), symbol("not")))(s)?;
    Ok((s, NOutputGatetype { nodes: (a,) }))
}

pub fn pass_en_switchtype(s: Span) -> IResult<Span, PassEnSwitchtype> {
    let (s, a) = alt((
        symbol("tranif0"),
        symbol("tranif1"),
        symbol("rtranif0"),
        symbol("rtranif1"),
    ))(s)?;
    Ok((s, PassEnSwitchtype { nodes: (a,) }))
}

pub fn pass_switchtype(s: Span) -> IResult<Span, PassSwitchtype> {
    let (s, a) = alt((symbol("tran"), symbol("rtran")))(s)?;
    Ok((s, PassSwitchtype { nodes: (a,) }))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use nom::combinator::*;

    #[test]
    fn test_cmos_switchtype() {
        parser_test!(cmos_switchtype, "cmos", Ok((_, _)));
        parser_test!(cmos_switchtype, "rcmos", Ok((_, _)));
    }

    #[test]
    fn test_enable_gatetype() {
        parser_test!(enable_gatetype, "bufif0", Ok((_, _)));
        parser_test!(enable_gatetype, "bufif1", Ok((_, _)));
        parser_test!(enable_gatetype, "notif0", Ok((_, _)));
        parser_test!(enable_gatetype, "notif1", Ok((_, _)));
    }

    #[test]
    fn test_mos_switchtype() {
        parser_test!(mos_switchtype, "nmos", Ok((_, _)));
        parser_test!(mos_switchtype, "pmos", Ok((_, _)));
        parser_test!(mos_switchtype, "rnmos", Ok((_, _)));
        parser_test!(mos_switchtype, "rpmos", Ok((_, _)));
    }

    #[test]
    fn test_n_input_gatetype() {
        parser_test!(n_input_gatetype, "and", Ok((_, _)));
        parser_test!(n_input_gatetype, "nand", Ok((_, _)));
        parser_test!(n_input_gatetype, "or", Ok((_, _)));
        parser_test!(n_input_gatetype, "nor", Ok((_, _)));
        parser_test!(n_input_gatetype, "xor", Ok((_, _)));
        parser_test!(n_input_gatetype, "xnor", Ok((_, _)));
    }

    #[test]
    fn test_n_output_gatetype() {
        parser_test!(n_output_gatetype, "buf", Ok((_, _)));
        parser_test!(n_output_gatetype, "not", Ok((_, _)));
    }

    #[test]
    fn test_pass_en_switchtype() {
        parser_test!(pass_en_switchtype, "tranif0", Ok((_, _)));
        parser_test!(pass_en_switchtype, "tranif1", Ok((_, _)));
        parser_test!(pass_en_switchtype, "rtranif0", Ok((_, _)));
        parser_test!(pass_en_switchtype, "rtranif1", Ok((_, _)));
    }

    #[test]
    fn test_pass_switchtype() {
        parser_test!(pass_switchtype, "tran", Ok((_, _)));
        parser_test!(pass_switchtype, "rtran", Ok((_, _)));
    }
}
