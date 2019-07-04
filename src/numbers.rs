use crate::utils::*;
use nom::branch::*;
use nom::bytes::complete::*;
use nom::character::complete::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum Number<'a> {
    IntegralNumber(IntegralNumber<'a>),
    RealNumber(RealNumber<'a>),
}

#[derive(Debug)]
pub enum IntegralNumber<'a> {
    DecimalNumber(DecimalNumber<'a>),
    OctalNumber(OctalNumber<'a>),
    BinaryNumber(BinaryNumber<'a>),
    HexNumber(HexNumber<'a>),
    UnsignedNumber(&'a str),
}

#[derive(Debug)]
pub enum RealNumber<'a> {
    FixedPointNumber(FixedPointNumber<'a>),
    FloatingPointNumber(FloatingPointNumber<'a>),
}

#[derive(Debug)]
pub struct DecimalNumber<'a> {
    pub size: Option<&'a str>,
    pub decimal_base: &'a str,
    pub decimal_value: &'a str,
}

#[derive(Debug)]
pub struct BinaryNumber<'a> {
    pub size: Option<&'a str>,
    pub binary_base: &'a str,
    pub binary_value: &'a str,
}

#[derive(Debug)]
pub struct OctalNumber<'a> {
    pub size: Option<&'a str>,
    pub octal_base: &'a str,
    pub octal_value: &'a str,
}

#[derive(Debug)]
pub struct HexNumber<'a> {
    pub size: Option<&'a str>,
    pub hex_base: &'a str,
    pub hex_value: &'a str,
}

#[derive(Debug)]
pub struct FixedPointNumber<'a> {
    pub integer_value: &'a str,
    pub fraction_value: &'a str,
}

#[derive(Debug)]
pub struct FloatingPointNumber<'a> {
    pub integer_value: &'a str,
    pub fraction_value: Option<&'a str>,
    pub exponent: &'a str,
    pub sign: Option<&'a str>,
    pub exponent_value: &'a str,
}

// -----------------------------------------------------------------------------

pub fn number(s: &str) -> IResult<&str, Number> {
    alt((real_number, integral_number))(s)
}

pub fn integral_number(s: &str) -> IResult<&str, Number> {
    let (s, x) = alt((
        octal_number,
        binary_number,
        hex_number,
        decimal_number,
        integral_unsigned_number,
    ))(s)?;
    Ok((s, Number::IntegralNumber(x)))
}

pub fn decimal_number(s: &str) -> IResult<&str, IntegralNumber> {
    let (s, (size, decimal_base, decimal_value)) = tuple((
        opt(size),
        decimal_base,
        alt((unsigned_number, x_number, z_number)),
    ))(s)?;
    Ok((
        s,
        IntegralNumber::DecimalNumber(DecimalNumber {
            size,
            decimal_base,
            decimal_value,
        }),
    ))
}

pub fn integral_unsigned_number(s: &str) -> IResult<&str, IntegralNumber> {
    let (s, x) = unsigned_number(s)?;
    Ok((s, IntegralNumber::UnsignedNumber(x)))
}

pub fn binary_number(s: &str) -> IResult<&str, IntegralNumber> {
    let (s, (size, binary_base, binary_value)) = tuple((opt(size), binary_base, binary_value))(s)?;
    Ok((
        s,
        IntegralNumber::BinaryNumber(BinaryNumber {
            size,
            binary_base,
            binary_value,
        }),
    ))
}

pub fn octal_number(s: &str) -> IResult<&str, IntegralNumber> {
    let (s, (size, octal_base, octal_value)) = tuple((opt(size), octal_base, octal_value))(s)?;
    Ok((
        s,
        IntegralNumber::OctalNumber(OctalNumber {
            size,
            octal_base,
            octal_value,
        }),
    ))
}

pub fn hex_number(s: &str) -> IResult<&str, IntegralNumber> {
    let (s, (size, hex_base, hex_value)) = tuple((opt(size), hex_base, hex_value))(s)?;
    Ok((
        s,
        IntegralNumber::HexNumber(HexNumber {
            size,
            hex_base,
            hex_value,
        }),
    ))
}

pub fn size(s: &str) -> IResult<&str, &str> {
    ws(size_impl)(s)
}

pub fn size_impl(s: &str) -> IResult<&str, &str> {
    let (s, x) = is_a("123456789")(s)?;
    fold_many0(alt((tag("_"), digit1)), x, |acc, item| {
        str_concat::concat(acc, item).unwrap()
    })(s)
}

pub fn real_number(s: &str) -> IResult<&str, Number> {
    let (s, x) = alt((floating_point_number, fixed_point_number))(s)?;
    Ok((s, Number::RealNumber(x)))
}

pub fn fixed_point_number(s: &str) -> IResult<&str, RealNumber> {
    let (s, (integer_value, _, fraction_value)) =
        tuple((unsigned_number, symbol("."), unsigned_number))(s)?;
    Ok((
        s,
        RealNumber::FixedPointNumber(FixedPointNumber {
            integer_value,
            fraction_value,
        }),
    ))
}

pub fn floating_point_number(s: &str) -> IResult<&str, RealNumber> {
    let (s, integer_value) = unsigned_number(s)?;
    let (s, fraction_value) = opt(tuple((symbol("."), unsigned_number)))(s)?;
    let (s, exponent) = alt((symbol("e"), symbol("E")))(s)?;
    let (s, sign) = opt(alt((symbol("+"), symbol("-"))))(s)?;
    let (s, exponent_value) = unsigned_number(s)?;

    let fraction_value = fraction_value.and_then(|(_, y)| Some(y));

    Ok((
        s,
        RealNumber::FloatingPointNumber(FloatingPointNumber {
            integer_value,
            fraction_value,
            exponent,
            sign,
            exponent_value,
        }),
    ))
}

pub fn unsigned_number(s: &str) -> IResult<&str, &str> {
    ws(unsigned_number_impl)(s)
}

pub fn unsigned_number_impl(s: &str) -> IResult<&str, &str> {
    let (s, x) = digit1(s)?;
    fold_many0(alt((tag("_"), digit1)), x, |acc, item| {
        str_concat::concat(acc, item).unwrap()
    })(s)
}

pub fn binary_value(s: &str) -> IResult<&str, &str> {
    ws(binary_value_impl)(s)
}

pub fn binary_value_impl(s: &str) -> IResult<&str, &str> {
    let (s, x) = is_a("01xXzZ?")(s)?;
    fold_many0(alt((tag("_"), is_a("01xXzZ?"))), x, |acc, item| {
        str_concat::concat(acc, item).unwrap()
    })(s)
}

pub fn octal_value(s: &str) -> IResult<&str, &str> {
    ws(octal_value_impl)(s)
}

pub fn octal_value_impl(s: &str) -> IResult<&str, &str> {
    let (s, x) = is_a("01234567xXzZ?")(s)?;
    fold_many0(alt((tag("_"), is_a("01234567xXzZ?"))), x, |acc, item| {
        str_concat::concat(acc, item).unwrap()
    })(s)
}

pub fn hex_value(s: &str) -> IResult<&str, &str> {
    ws(hex_value_impl)(s)
}

pub fn hex_value_impl(s: &str) -> IResult<&str, &str> {
    let (s, x) = is_a("0123456789abcdefABCDEFxXzZ?")(s)?;
    fold_many0(
        alt((tag("_"), is_a("0123456789abcdefABCDEFxXzZ?"))),
        x,
        |acc, item| str_concat::concat(acc, item).unwrap(),
    )(s)
}

pub fn decimal_base(s: &str) -> IResult<&str, &str> {
    ws(decimal_base_impl)(s)
}

pub fn decimal_base_impl(s: &str) -> IResult<&str, &str> {
    alt((tag_no_case("'d"), tag_no_case("'sd")))(s)
}

pub fn binary_base(s: &str) -> IResult<&str, &str> {
    ws(binary_base_impl)(s)
}

pub fn binary_base_impl(s: &str) -> IResult<&str, &str> {
    alt((tag_no_case("'b"), tag_no_case("'sb")))(s)
}

pub fn octal_base(s: &str) -> IResult<&str, &str> {
    ws(octal_base_impl)(s)
}

pub fn octal_base_impl(s: &str) -> IResult<&str, &str> {
    alt((tag_no_case("'o"), tag_no_case("'so")))(s)
}

pub fn hex_base(s: &str) -> IResult<&str, &str> {
    ws(hex_base_impl)(s)
}

pub fn hex_base_impl(s: &str) -> IResult<&str, &str> {
    alt((tag_no_case("'h"), tag_no_case("'sh")))(s)
}

pub fn x_number(s: &str) -> IResult<&str, &str> {
    ws(x_number_impl)(s)
}

pub fn x_number_impl(s: &str) -> IResult<&str, &str> {
    let (s, x) = tag_no_case("x")(s)?;
    fold_many0(alt((tag("_"), is_a("_"))), x, |acc, item| {
        str_concat::concat(acc, item).unwrap()
    })(s)
}

pub fn z_number(s: &str) -> IResult<&str, &str> {
    ws(z_number_impl)(s)
}

pub fn z_number_impl(s: &str) -> IResult<&str, &str> {
    let (s, x) = alt((tag_no_case("z"), tag("?")))(s)?;
    fold_many0(alt((tag("_"), is_a("_"))), x, |acc, item| {
        str_concat::concat(acc, item).unwrap()
    })(s)
}

pub fn unbased_unsized_literal(s: &str) -> IResult<&str, &str> {
    alt((symbol("'0"), symbol("'1"), symbol("'z"), symbol("'x")))(s)
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        assert_eq!(
            format!("{:?}", all_consuming(number)("659")),
            "Ok((\"\", IntegralNumber(UnsignedNumber(\"659\"))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("'h 837FF")),
            "Ok((\"\", IntegralNumber(HexNumber(HexNumber { size: None, hex_base: \"\\\'h\", hex_value: \"837FF\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("'o7460")),
            "Ok((\"\", IntegralNumber(OctalNumber(OctalNumber { size: None, octal_base: \"\\\'o\", octal_value: \"7460\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("4af")),
            "Err(Error((\"af\", Eof)))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("4'b1001")),
            "Ok((\"\", IntegralNumber(BinaryNumber(BinaryNumber { size: Some(\"4\"), binary_base: \"\\\'b\", binary_value: \"1001\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("5 'D 3")),
            "Ok((\"\", IntegralNumber(DecimalNumber(DecimalNumber { size: Some(\"5\"), decimal_base: \"\\\'D\", decimal_value: \"3\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("3'b01x")),
            "Ok((\"\", IntegralNumber(BinaryNumber(BinaryNumber { size: Some(\"3\"), binary_base: \"\\\'b\", binary_value: \"01x\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("12'hx")),
            "Ok((\"\", IntegralNumber(HexNumber(HexNumber { size: Some(\"12\"), hex_base: \"\\\'h\", hex_value: \"x\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("16'hz")),
            "Ok((\"\", IntegralNumber(HexNumber(HexNumber { size: Some(\"16\"), hex_base: \"\\\'h\", hex_value: \"z\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("8 'd -6")),
            "Err(Error((\"\\\'d -6\", Eof)))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("4 'shf")),
            "Ok((\"\", IntegralNumber(HexNumber(HexNumber { size: Some(\"4\"), hex_base: \"\\\'sh\", hex_value: \"f\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("16'sd?")),
            "Ok((\"\", IntegralNumber(DecimalNumber(DecimalNumber { size: Some(\"16\"), decimal_base: \"\\\'sd\", decimal_value: \"?\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("27_195_000")),
            "Ok((\"\", IntegralNumber(UnsignedNumber(\"27_195_000\"))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("16'b0011_0101_0001_1111")),
            "Ok((\"\", IntegralNumber(BinaryNumber(BinaryNumber { size: Some(\"16\"), binary_base: \"\\\'b\", binary_value: \"0011_0101_0001_1111\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("32 'h 12ab_f001")),
            "Ok((\"\", IntegralNumber(HexNumber(HexNumber { size: Some(\"32\"), hex_base: \"\\\'h\", hex_value: \"12ab_f001\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("1.2")),
            "Ok((\"\", RealNumber(FixedPointNumber(FixedPointNumber { integer_value: \"1\", fraction_value: \"2\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("0.1")),
            "Ok((\"\", RealNumber(FixedPointNumber(FixedPointNumber { integer_value: \"0\", fraction_value: \"1\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("2394.26331")),
            "Ok((\"\", RealNumber(FixedPointNumber(FixedPointNumber { integer_value: \"2394\", fraction_value: \"26331\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("1.2E12")),
            "Ok((\"\", RealNumber(FloatingPointNumber(FloatingPointNumber { integer_value: \"1\", fraction_value: Some(\"2\"), exponent: \"E\", sign: None, exponent_value: \"12\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("1.30e-2")),
            "Ok((\"\", RealNumber(FloatingPointNumber(FloatingPointNumber { integer_value: \"1\", fraction_value: Some(\"30\"), exponent: \"e\", sign: Some(\"-\"), exponent_value: \"2\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("0.1e-0")),
            "Ok((\"\", RealNumber(FloatingPointNumber(FloatingPointNumber { integer_value: \"0\", fraction_value: Some(\"1\"), exponent: \"e\", sign: Some(\"-\"), exponent_value: \"0\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("23E10")),
            "Ok((\"\", RealNumber(FloatingPointNumber(FloatingPointNumber { integer_value: \"23\", fraction_value: None, exponent: \"E\", sign: None, exponent_value: \"10\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("29E-2")),
            "Ok((\"\", RealNumber(FloatingPointNumber(FloatingPointNumber { integer_value: \"29\", fraction_value: None, exponent: \"E\", sign: Some(\"-\"), exponent_value: \"2\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("236.123_763_e-12")),
            "Ok((\"\", RealNumber(FloatingPointNumber(FloatingPointNumber { integer_value: \"236\", fraction_value: Some(\"123_763_\"), exponent: \"e\", sign: Some(\"-\"), exponent_value: \"12\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(".12")),
            "Err(Error((\".12\", Digit)))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("9.")),
            "Err(Error((\".\", Eof)))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("4.E3")),
            "Err(Error((\".E3\", Eof)))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(".2e-7")),
            "Err(Error((\".2e-7\", Digit)))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(unbased_unsized_literal)("'0")),
            "Ok((\"\", \"\\\'0\"))"
        );
    }
}
