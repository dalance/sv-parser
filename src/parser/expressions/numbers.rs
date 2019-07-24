use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::bytes::complete::*;
use nom::character::complete::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;
use nom_packrat::packrat_parser;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum Number {
    IntegralNumber(Box<IntegralNumber>),
    RealNumber(Box<RealNumber>),
}

#[derive(Clone, Debug, Node)]
pub enum IntegralNumber {
    DecimalNumber(Box<DecimalNumber>),
    OctalNumber(Box<OctalNumber>),
    BinaryNumber(Box<BinaryNumber>),
    HexNumber(Box<HexNumber>),
}

#[derive(Clone, Debug, Node)]
pub enum DecimalNumber {
    UnsignedNumber(Box<UnsignedNumber>),
    BaseUnsigned(Box<DecimalNumberBaseUnsigned>),
    BaseXNumber(Box<DecimalNumberBaseXNumber>),
    BaseZNumber(Box<DecimalNumberBaseZNumber>),
}

#[derive(Clone, Debug, Node)]
pub struct DecimalNumberBaseUnsigned {
    pub nodes: (Option<Size>, DecimalBase, UnsignedNumber),
}

#[derive(Clone, Debug, Node)]
pub struct DecimalNumberBaseXNumber {
    pub nodes: (Option<Size>, DecimalBase, XNumber),
}

#[derive(Clone, Debug, Node)]
pub struct DecimalNumberBaseZNumber {
    pub nodes: (Option<Size>, DecimalBase, ZNumber),
}

#[derive(Clone, Debug, Node)]
pub struct BinaryNumber {
    pub nodes: (Option<Size>, BinaryBase, BinaryValue),
}

#[derive(Clone, Debug, Node)]
pub struct OctalNumber {
    pub nodes: (Option<Size>, OctalBase, OctalValue),
}

#[derive(Clone, Debug, Node)]
pub struct HexNumber {
    pub nodes: (Option<Size>, HexBase, HexValue),
}

#[derive(Clone, Debug, Node)]
pub enum Sign {
    Plus(Box<Symbol>),
    Minus(Box<Symbol>),
}

#[derive(Clone, Debug, Node)]
pub struct Size {
    pub nodes: (NonZeroUnsignedNumber,),
}

#[derive(Clone, Debug, Node)]
pub struct NonZeroUnsignedNumber {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

#[derive(Clone, Debug, Node)]
pub enum RealNumber {
    FixedPointNumber(Box<FixedPointNumber>),
    Floating(Box<RealNumberFloating>),
}

#[derive(Clone, Debug, Node)]
pub struct RealNumberFloating {
    pub nodes: (
        UnsignedNumber,
        Option<(Symbol, UnsignedNumber)>,
        Exp,
        Option<Sign>,
        UnsignedNumber,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct FixedPointNumber {
    pub nodes: (UnsignedNumber, Symbol, UnsignedNumber),
}

#[derive(Clone, Debug, Node)]
pub struct Exp {
    pub nodes: (Symbol,),
}

#[derive(Clone, Debug, Node)]
pub struct UnsignedNumber {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

#[derive(Clone, Debug, Node)]
pub struct BinaryValue {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

#[derive(Clone, Debug, Node)]
pub struct OctalValue {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

#[derive(Clone, Debug, Node)]
pub struct HexValue {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

#[derive(Clone, Debug, Node)]
pub struct DecimalBase {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

#[derive(Clone, Debug, Node)]
pub struct BinaryBase {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

#[derive(Clone, Debug, Node)]
pub struct OctalBase {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

#[derive(Clone, Debug, Node)]
pub struct HexBase {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

#[derive(Clone, Debug, Node)]
pub struct XNumber {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

#[derive(Clone, Debug, Node)]
pub struct ZNumber {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

#[derive(Clone, Debug, Node)]
pub struct UnbasedUnsizedLiteral {
    pub nodes: (Symbol,),
}

// -----------------------------------------------------------------------------

#[packrat_parser]
#[parser]
pub fn number(s: Span) -> IResult<Span, Number> {
    alt((
        map(real_number, |x| Number::RealNumber(Box::new(x))),
        map(integral_number, |x| Number::IntegralNumber(Box::new(x))),
    ))(s)
}

#[parser]
pub fn integral_number(s: Span) -> IResult<Span, IntegralNumber> {
    alt((
        map(octal_number, |x| IntegralNumber::OctalNumber(Box::new(x))),
        map(binary_number, |x| IntegralNumber::BinaryNumber(Box::new(x))),
        map(hex_number, |x| IntegralNumber::HexNumber(Box::new(x))),
        map(decimal_number, |x| {
            IntegralNumber::DecimalNumber(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn decimal_number(s: Span) -> IResult<Span, DecimalNumber> {
    alt((
        decimal_number_base_unsigned,
        decimal_number_base_x_number,
        decimal_number_base_z_number,
        map(unsigned_number, |x| {
            DecimalNumber::UnsignedNumber(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn decimal_number_base_unsigned(s: Span) -> IResult<Span, DecimalNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = decimal_base(s)?;
    let (s, c) = unsigned_number(s)?;
    Ok((
        s,
        DecimalNumber::BaseUnsigned(Box::new(DecimalNumberBaseUnsigned { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn decimal_number_base_x_number(s: Span) -> IResult<Span, DecimalNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = decimal_base(s)?;
    let (s, c) = x_number(s)?;
    Ok((
        s,
        DecimalNumber::BaseXNumber(Box::new(DecimalNumberBaseXNumber { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn decimal_number_base_z_number(s: Span) -> IResult<Span, DecimalNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = decimal_base(s)?;
    let (s, c) = z_number(s)?;
    Ok((
        s,
        DecimalNumber::BaseZNumber(Box::new(DecimalNumberBaseZNumber { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn binary_number(s: Span) -> IResult<Span, BinaryNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = binary_base(s)?;
    let (s, c) = binary_value(s)?;
    Ok((s, BinaryNumber { nodes: (a, b, c) }))
}

#[parser]
pub fn octal_number(s: Span) -> IResult<Span, OctalNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = octal_base(s)?;
    let (s, c) = octal_value(s)?;
    Ok((s, OctalNumber { nodes: (a, b, c) }))
}

#[parser]
pub fn hex_number(s: Span) -> IResult<Span, HexNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = hex_base(s)?;
    let (s, c) = hex_value(s)?;
    Ok((s, HexNumber { nodes: (a, b, c) }))
}

#[parser]
pub fn sign(s: Span) -> IResult<Span, Sign> {
    alt((
        map(symbol("+"), |x| Sign::Plus(Box::new(x))),
        map(symbol("-"), |x| Sign::Minus(Box::new(x))),
    ))(s)
}

#[parser]
pub fn size(s: Span) -> IResult<Span, Size> {
    let (s, a) = non_zero_unsigned_number(s)?;
    Ok((s, Size { nodes: (a,) }))
}

#[parser]
pub fn non_zero_unsigned_number(s: Span) -> IResult<Span, NonZeroUnsignedNumber> {
    let (s, a) = ws(non_zero_unsigned_number_impl)(s)?;
    Ok((s, NonZeroUnsignedNumber { nodes: a }))
}

#[parser]
pub fn non_zero_unsigned_number_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = is_a("123456789")(s)?;
    let (s, a) = fold_many0(alt((tag("_"), digit1)), a, |acc, item| {
        concat(acc, item).unwrap()
    })(s)?;
    Ok((s, a.into()))
}

#[parser]
pub fn real_number(s: Span) -> IResult<Span, RealNumber> {
    alt((
        real_number_floating,
        map(fixed_point_number, |x| {
            RealNumber::FixedPointNumber(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn real_number_floating(s: Span) -> IResult<Span, RealNumber> {
    let (s, a) = unsigned_number(s)?;
    let (s, b) = opt(pair(symbol("."), unsigned_number))(s)?;
    let (s, c) = exp(s)?;
    let (s, d) = opt(sign)(s)?;
    let (s, e) = unsigned_number(s)?;
    Ok((
        s,
        RealNumber::Floating(Box::new(RealNumberFloating {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[parser]
pub fn fixed_point_number(s: Span) -> IResult<Span, FixedPointNumber> {
    let (s, a) = unsigned_number(s)?;
    let (s, b) = map(tag("."), |x: Span| Symbol {
        nodes: (x.into(), vec![]),
    })(s)?;
    let (s, c) = unsigned_number(s)?;
    Ok((s, FixedPointNumber { nodes: (a, b, c) }))
}

#[parser]
pub fn exp(s: Span) -> IResult<Span, Exp> {
    let (s, a) = alt((symbol("e"), symbol("E")))(s)?;
    Ok((s, Exp { nodes: (a,) }))
}

#[parser]
pub fn unsigned_number(s: Span) -> IResult<Span, UnsignedNumber> {
    let (s, a) = ws(unsigned_number_impl)(s)?;
    Ok((s, UnsignedNumber { nodes: a }))
}

#[parser]
pub fn unsigned_number_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = digit1(s)?;
    let (s, a) = fold_many0(alt((tag("_"), digit1)), a, |acc, item| {
        concat(acc, item).unwrap()
    })(s)?;
    Ok((s, a.into()))
}

#[parser]
pub fn binary_value(s: Span) -> IResult<Span, BinaryValue> {
    let (s, a) = ws(binary_value_impl)(s)?;
    Ok((s, BinaryValue { nodes: a }))
}

#[parser]
pub fn binary_value_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = is_a("01xXzZ?")(s)?;
    let (s, a) = fold_many0(alt((tag("_"), is_a("01xXzZ?"))), a, |acc, item| {
        concat(acc, item).unwrap()
    })(s)?;
    Ok((s, a.into()))
}

#[parser]
pub fn octal_value(s: Span) -> IResult<Span, OctalValue> {
    let (s, a) = ws(octal_value_impl)(s)?;
    Ok((s, OctalValue { nodes: a }))
}

#[parser]
pub fn octal_value_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = is_a("01234567xXzZ?")(s)?;
    let (s, a) = fold_many0(alt((tag("_"), is_a("01234567xXzZ?"))), a, |acc, item| {
        concat(acc, item).unwrap()
    })(s)?;
    Ok((s, a.into()))
}

#[parser]
pub fn hex_value(s: Span) -> IResult<Span, HexValue> {
    let (s, a) = ws(hex_value_impl)(s)?;
    Ok((s, HexValue { nodes: a }))
}

#[parser]
pub fn hex_value_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = is_a("0123456789abcdefABCDEFxXzZ?")(s)?;
    let (s, a) = fold_many0(
        alt((tag("_"), is_a("0123456789abcdefABCDEFxXzZ?"))),
        a,
        |acc, item| concat(acc, item).unwrap(),
    )(s)?;
    Ok((s, a.into()))
}

#[parser]
pub fn decimal_base(s: Span) -> IResult<Span, DecimalBase> {
    let (s, a) = ws(decimal_base_impl)(s)?;
    Ok((s, DecimalBase { nodes: a }))
}

#[parser]
pub fn decimal_base_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = alt((tag_no_case("'d"), tag_no_case("'sd")))(s)?;
    Ok((s, a.into()))
}

#[parser]
pub fn binary_base(s: Span) -> IResult<Span, BinaryBase> {
    let (s, a) = ws(binary_base_impl)(s)?;
    Ok((s, BinaryBase { nodes: a }))
}

#[parser]
pub fn binary_base_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = alt((tag_no_case("'b"), tag_no_case("'sb")))(s)?;
    Ok((s, a.into()))
}

#[parser]
pub fn octal_base(s: Span) -> IResult<Span, OctalBase> {
    let (s, a) = ws(octal_base_impl)(s)?;
    Ok((s, OctalBase { nodes: a }))
}

#[parser]
pub fn octal_base_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = alt((tag_no_case("'o"), tag_no_case("'so")))(s)?;
    Ok((s, a.into()))
}

#[parser]
pub fn hex_base(s: Span) -> IResult<Span, HexBase> {
    let (s, a) = ws(hex_base_impl)(s)?;
    Ok((s, HexBase { nodes: a }))
}

#[parser]
pub fn hex_base_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = alt((tag_no_case("'h"), tag_no_case("'sh")))(s)?;
    Ok((s, a.into()))
}

#[parser]
pub fn x_number(s: Span) -> IResult<Span, XNumber> {
    let (s, a) = ws(x_number_impl)(s)?;
    Ok((s, XNumber { nodes: a }))
}

#[parser]
pub fn x_number_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = tag_no_case("x")(s)?;
    let (s, a) = fold_many0(alt((tag("_"), is_a("_"))), a, |acc, item| {
        concat(acc, item).unwrap()
    })(s)?;
    Ok((s, a.into()))
}

#[parser]
pub fn z_number(s: Span) -> IResult<Span, ZNumber> {
    let (s, a) = ws(z_number_impl)(s)?;
    Ok((s, ZNumber { nodes: a }))
}

#[parser]
pub fn z_number_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = alt((tag_no_case("z"), tag("?")))(s)?;
    let (s, a) = fold_many0(alt((tag("_"), is_a("_"))), a, |acc, item| {
        concat(acc, item).unwrap()
    })(s)?;
    Ok((s, a.into()))
}

#[parser]
pub fn unbased_unsized_literal(s: Span) -> IResult<Span, UnbasedUnsizedLiteral> {
    let (s, a) = alt((symbol("'0"), symbol("'1"), symbol("'z"), symbol("'x")))(s)?;
    Ok((s, UnbasedUnsizedLiteral { nodes: (a,) }))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_number() {
        parser_test!(number, "659", Ok((_, Number::IntegralNumber(_))));
        parser_test!(number, "'h 837FF", Ok((_, Number::IntegralNumber(_))));
        parser_test!(number, "'h 837FF", Ok((_, Number::IntegralNumber(_))));
        parser_test!(number, "'o7460", Ok((_, Number::IntegralNumber(_))));
        parser_test!(number, "'4af", Err(_));
        parser_test!(number, "4'b1001", Ok((_, Number::IntegralNumber(_))));
        parser_test!(number, "5 'D 3", Ok((_, Number::IntegralNumber(_))));
        parser_test!(number, "3'b01x", Ok((_, Number::IntegralNumber(_))));
        parser_test!(number, "12'hx", Ok((_, Number::IntegralNumber(_))));
        parser_test!(number, "16'hz", Ok((_, Number::IntegralNumber(_))));
        parser_test!(number, "8 'd -6", Err(_));
        parser_test!(number, "4 'shf", Ok((_, Number::IntegralNumber(_))));
        parser_test!(number, "16'sd?", Ok((_, Number::IntegralNumber(_))));
        parser_test!(number, "27_195_000", Ok((_, Number::IntegralNumber(_))));
        parser_test!(
            number,
            "16'b0011_0101_0001_1111",
            Ok((_, Number::IntegralNumber(_)))
        );
        parser_test!(
            number,
            "32 'h 12ab_f001",
            Ok((_, Number::IntegralNumber(_)))
        );
        parser_test!(number, "1.2", Ok((_, Number::RealNumber(_))));
        parser_test!(number, "0.1", Ok((_, Number::RealNumber(_))));
        parser_test!(number, "2394.26331", Ok((_, Number::RealNumber(_))));
        parser_test!(number, "1.2E12", Ok((_, Number::RealNumber(_))));
        parser_test!(number, "1.30e-2", Ok((_, Number::RealNumber(_))));
        parser_test!(number, "0.1e-0", Ok((_, Number::RealNumber(_))));
        parser_test!(number, "23E10", Ok((_, Number::RealNumber(_))));
        parser_test!(number, "29E-2", Ok((_, Number::RealNumber(_))));
        parser_test!(number, "236.123_763_e-12", Ok((_, Number::RealNumber(_))));
        parser_test!(number, ".12", Err(_));
        parser_test!(number, "9.", Err(_));
        parser_test!(number, "4.E3", Err(_));
        parser_test!(number, ".2e-7", Err(_));
    }

    #[test]
    fn test_unbased_unsized_literal() {
        parser_test!(unbased_unsized_literal, "'0", Ok((_, _)));
        parser_test!(unbased_unsized_literal, "'1", Ok((_, _)));
        parser_test!(unbased_unsized_literal, "'x", Ok((_, _)));
        parser_test!(unbased_unsized_literal, "'z", Ok((_, _)));
    }
}
