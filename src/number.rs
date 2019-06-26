use crate::ast::*;
use nom::branch::*;
use nom::bytes::complete::*;
use nom::character::complete::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

pub fn number(s: &str) -> IResult<&str, Number> {
    alt((integral_number, real_number))(s)
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
    let (s, (size, _, decimal_base, _, decimal_number)) = tuple((
        opt(size),
        space0,
        decimal_base,
        space0,
        alt((unsigned_number, x_number, z_number)),
    ))(s)?;
    Ok((
        s,
        IntegralNumber::DecimalNumber(DecimalNumber {
            size,
            decimal_base,
            decimal_number,
        }),
    ))
}

pub fn integral_unsigned_number(s: &str) -> IResult<&str, IntegralNumber> {
    let (s, x) = unsigned_number(s)?;
    Ok((s, IntegralNumber::UnsignedNumber(x)))
}

pub fn binary_number(s: &str) -> IResult<&str, IntegralNumber> {
    let (s, (size, _, binary_base, _, binary_value)) =
        tuple((opt(size), space0, binary_base, space0, binary_value))(s)?;
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
    let (s, (size, _, octal_base, _, octal_value)) =
        tuple((opt(size), space0, octal_base, space0, octal_value))(s)?;
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
    let (s, (size, _, hex_base, _, hex_value)) =
        tuple((opt(size), space0, hex_base, space0, hex_value))(s)?;
    Ok((
        s,
        IntegralNumber::HexNumber(HexNumber {
            size,
            hex_base,
            hex_value,
        }),
    ))
}

// sign

pub fn size(s: &str) -> IResult<&str, Vec<&str>> {
    let (s, x) = is_a("123456789")(s)?;
    let (s, x) = fold_many0(alt((tag("_"), digit1)), vec![x], |mut acc: Vec<_>, item| {
        acc.push(item);
        acc
    })(s)?;
    Ok((s, x))
}

pub fn real_number(s: &str) -> IResult<&str, Number> {
    let (s, x) = alt((fixed_point_number, floating_point_number))(s)?;
    Ok((s, Number::RealNumber(x)))
}

pub fn fixed_point_number(s: &str) -> IResult<&str, RealNumber> {
    Ok((s, RealNumber::FixedPointNumber))
}

pub fn floating_point_number(s: &str) -> IResult<&str, RealNumber> {
    Ok((s, RealNumber::FloatingPointNumber))
}

// exp

pub fn unsigned_number(s: &str) -> IResult<&str, Vec<&str>> {
    let (s, x) = digit1(s)?;
    fold_many0(alt((tag("_"), digit1)), vec![x], |mut acc: Vec<_>, item| {
        acc.push(item);
        acc
    })(s)
}

pub fn binary_value(s: &str) -> IResult<&str, Vec<&str>> {
    let (s, x) = is_a("01xXzZ?")(s)?;
    fold_many0(
        alt((tag("_"), is_a("01xXzZ?"))),
        vec![x],
        |mut acc: Vec<_>, item| {
            acc.push(item);
            acc
        },
    )(s)
}

pub fn octal_value(s: &str) -> IResult<&str, Vec<&str>> {
    let (s, x) = is_a("01234567xXzZ?")(s)?;
    fold_many0(
        alt((tag("_"), is_a("01234567xXzZ?"))),
        vec![x],
        |mut acc: Vec<_>, item| {
            acc.push(item);
            acc
        },
    )(s)
}

pub fn hex_value(s: &str) -> IResult<&str, Vec<&str>> {
    let (s, x) = is_a("0123456789abcdefABCDEFxXzZ?")(s)?;
    fold_many0(
        alt((tag("_"), is_a("0123456789abcdefABCDEFxXzZ?"))),
        vec![x],
        |mut acc: Vec<_>, item| {
            acc.push(item);
            acc
        },
    )(s)
}

pub fn decimal_base(s: &str) -> IResult<&str, &str> {
    alt((
        tag("'d"),
        tag("'sd"),
        tag("'Sd"),
        tag("'D"),
        tag("'sD"),
        tag("'SD"),
    ))(s)
}

pub fn binary_base(s: &str) -> IResult<&str, &str> {
    alt((
        tag("'b"),
        tag("'sb"),
        tag("'Sb"),
        tag("'B"),
        tag("'sB"),
        tag("'SB"),
    ))(s)
}

pub fn octal_base(s: &str) -> IResult<&str, &str> {
    alt((
        tag("'o"),
        tag("'so"),
        tag("'So"),
        tag("'O"),
        tag("'sO"),
        tag("'SO"),
    ))(s)
}

pub fn hex_base(s: &str) -> IResult<&str, &str> {
    alt((
        tag("'h"),
        tag("'sh"),
        tag("'Sh"),
        tag("'H"),
        tag("'sH"),
        tag("'SH"),
    ))(s)
}

pub fn x_number(s: &str) -> IResult<&str, Vec<&str>> {
    let (s, x) = alt((tag("x"), tag("X")))(s)?;
    fold_many0(
        alt((tag("_"), is_a("_"))),
        vec![x],
        |mut acc: Vec<_>, item| {
            acc.push(item);
            acc
        },
    )(s)
}

pub fn z_number(s: &str) -> IResult<&str, Vec<&str>> {
    let (s, x) = alt((tag("z"), tag("Z"), tag("?")))(s)?;
    fold_many0(
        alt((tag("_"), is_a("_"))),
        vec![x],
        |mut acc: Vec<_>, item| {
            acc.push(item);
            acc
        },
    )(s)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        assert_eq!(
            format!("{:?}", all_consuming(number)("659")),
            "Ok((\"\", IntegralNumber(UnsignedNumber([\"659\"]))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("'h 837FF")),
            "Ok((\"\", IntegralNumber(HexNumber(HexNumber { size: None, hex_base: \"\\\'h\", hex_value: [\"837FF\"] }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("'o7460")),
            "Ok((\"\", IntegralNumber(OctalNumber(OctalNumber { size: None, octal_base: \"\\\'o\", octal_value: [\"7460\"] }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("4af")),
            "Err(Error((\"af\", Eof)))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("4'b1001")),
            "Ok((\"\", IntegralNumber(BinaryNumber(BinaryNumber { size: Some([\"4\"]), binary_base: \"\\\'b\", binary_value: [\"1001\"] }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("5 'D 3")),
            "Ok((\"\", IntegralNumber(DecimalNumber(DecimalNumber { size: Some([\"5\"]), decimal_base: \"\\\'D\", decimal_number: [\"3\"] }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("3'b01x")),
            "Ok((\"\", IntegralNumber(BinaryNumber(BinaryNumber { size: Some([\"3\"]), binary_base: \"\\\'b\", binary_value: [\"01x\"] }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("12'hx")),
            "Ok((\"\", IntegralNumber(HexNumber(HexNumber { size: Some([\"12\"]), hex_base: \"\\\'h\", hex_value: [\"x\"] }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("16'hz")),
            "Ok((\"\", IntegralNumber(HexNumber(HexNumber { size: Some([\"16\"]), hex_base: \"\\\'h\", hex_value: [\"z\"] }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("8 'd -6")),
            "Err(Error((\" \\\'d -6\", Eof)))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("4 'shf")),
            "Ok((\"\", IntegralNumber(HexNumber(HexNumber { size: Some([\"4\"]), hex_base: \"\\\'sh\", hex_value: [\"f\"] }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("16'sd?")),
            "Ok((\"\", IntegralNumber(DecimalNumber(DecimalNumber { size: Some([\"16\"]), decimal_base: \"\\\'sd\", decimal_number: [\"?\"] }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("27_195_000")),
            "Ok((\"\", IntegralNumber(UnsignedNumber([\"27\", \"_\", \"195\", \"_\", \"000\"]))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("16'b0011_0101_0001_1111")),
            "Ok((\"\", IntegralNumber(BinaryNumber(BinaryNumber { size: Some([\"16\"]), binary_base: \"\\\'b\", binary_value: [\"0011\", \"_\", \"0101\", \"_\", \"0001\", \"_\", \"1111\"] }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("32 'h 12ab_f001")),
            "Ok((\"\", IntegralNumber(HexNumber(HexNumber { size: Some([\"32\"]), hex_base: \"\\\'h\", hex_value: [\"12ab\", \"_\", \"f001\"] }))))"
        );
    }
}
