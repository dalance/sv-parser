use nom::branch::*;
use nom::bytes::complete::*;
use nom::character::complete::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;
use str_concat::concat;

pub fn preprocessor_text(s: &str) -> IResult<&str, &str> {
    alt((multispace1, comment, string_literal, other))(s)
}

fn comment(s: &str) -> IResult<&str, &str> {
    alt((one_line_comment, block_comment))(s)
}

fn one_line_comment(s: &str) -> IResult<&str, &str> {
    let (s, a) = tag("//")(s)?;
    let (s, b) = is_not("\n")(s)?;
    let a = concat(a, b).unwrap();
    Ok((s, a))
}

fn block_comment(s: &str) -> IResult<&str, &str> {
    let (s, a) = tag("/*")(s)?;
    let (s, b) = is_not("*/")(s)?;
    let (s, c) = tag("*/")(s)?;
    let a = concat(a, b).unwrap();
    let a = concat(a, c).unwrap();
    Ok((s, a))
}

fn string_literal(s: &str) -> IResult<&str, &str> {
    let (s, a) = tag("\"")(s)?;
    let (s, b) = many0(alt((
        is_not("\\\""),
        map(pair(tag("\\"), take(1usize)), |(x, y)| {
            concat(x, y).unwrap()
        }),
    )))(s)?;
    let (s, c) = tag("\"")(s)?;

    let mut ret = None;
    for x in b {
        ret = if let Some(ret) = ret {
            Some(concat(ret, x).unwrap())
        } else {
            Some(x)
        };
    }

    let a = if let Some(b) = ret {
        let a = concat(a, b).unwrap();
        let a = concat(a, c).unwrap();
        a
    } else {
        let a = concat(a, c).unwrap();
        a
    };

    Ok((s, a))
}

fn other(s: &str) -> IResult<&str, &str> {
    let (s, a) = many1(alt((
        is_not("\"`/"),
        terminated(tag("/"), peek(not(alt((tag("/"), tag("*")))))),
    )))(s)?;

    let mut ret = None;
    for x in a {
        ret = if let Some(ret) = ret {
            Some(concat(ret, x).unwrap())
        } else {
            Some(x)
        };
    }
    let a = ret.unwrap();
    Ok((s, a))
}

fn ws<'a, F>(f: F) -> impl Fn(&'a str) -> IResult<&'a str, &'a str>
where
    F: Fn(&'a str) -> IResult<&'a str, &'a str>,
{
    move |s: &'a str| {
        let (s, x) = f(s)?;
        let (s, y) = multispace0(s)?;
        Ok((s, concat(x, y).unwrap()))
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
