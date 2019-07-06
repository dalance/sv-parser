use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct TfCall<'a> {
    pub identifier: ScopedIdentifier<'a>,
    pub attribute: Vec<AttributeInstance<'a>>,
    pub argument: Option<ListOfArguments<'a>>,
}

#[derive(Debug)]
pub struct SystemTfCall<'a> {
    pub identifier: Identifier<'a>,
    pub argument: Option<ListOfArguments<'a>>,
    pub data_type: Option<DataType<'a>>,
    pub expression: Option<Vec<Expression<'a>>>,
    pub clocking_event: Option<ClockingEvent<'a>>,
}

#[derive(Debug)]
pub enum SubroutineCall<'a> {
    Tf(Box<TfCall<'a>>),
    SystemTf(Box<SystemTfCall<'a>>),
    Method(Box<MethodCall<'a>>),
    Randomize(Box<RandomizeCall<'a>>),
    StdRandomize(Box<RandomizeCall<'a>>),
}

#[derive(Debug)]
pub struct ListOfArguments<'a> {
    pub unnamed: Vec<Expression<'a>>,
    pub named: Vec<(Identifier<'a>, Option<Expression<'a>>)>,
}

#[derive(Debug)]
pub struct MethodCall<'a> {
    pub root: MethodCallRoot<'a>,
    pub body: MethodCallBody<'a>,
}

#[derive(Debug)]
pub enum MethodCallRoot<'a> {
    Primary(Primary<'a>),
    ImplicitClassHandle(Scope<'a>),
}

#[derive(Debug)]
pub enum MethodCallBody<'a> {
    User(MethodCallBodyUser<'a>),
    Array(ArrayManipulationCall<'a>),
    Randomize(RandomizeCall<'a>),
}

#[derive(Debug)]
pub struct MethodCallBodyUser<'a> {
    pub identifier: Identifier<'a>,
    pub attribute: Vec<AttributeInstance<'a>>,
    pub argument: Option<ListOfArguments<'a>>,
}

#[derive(Debug)]
pub struct ArrayManipulationCall<'a> {
    pub name: ArrayMethodName<'a>,
    pub attribute: Vec<AttributeInstance<'a>>,
    pub argument: Option<ListOfArguments<'a>>,
    pub with: Option<Expression<'a>>,
}

#[derive(Debug)]
pub struct RandomizeCall<'a> {
    pub attribute: Vec<AttributeInstance<'a>>,
    pub argument: Vec<Identifier<'a>>,
    pub with: Vec<Identifier<'a>>,
    pub constraint_block: Option<ConstraintBlock<'a>>,
}

#[derive(Debug)]
pub enum ArrayMethodName<'a> {
    Identifier(Identifier<'a>),
    Unique,
    And,
    Or,
    Xor,
}

// -----------------------------------------------------------------------------

pub fn constant_function_call(s: &str) -> IResult<&str, SubroutineCall> {
    function_subroutine_call(s)
}

pub fn tf_call(s: &str) -> IResult<&str, TfCall> {
    let (s, x) = ps_or_hierarchical_tf_identifier(s)?;
    let (s, y) = many0(attribute_instance)(s)?;
    let (s, z) = opt(paren(list_of_arguments))(s)?;
    Ok((
        s,
        TfCall {
            identifier: x,
            attribute: y,
            argument: z,
        },
    ))
}

pub fn system_tf_call(s: &str) -> IResult<&str, SystemTfCall> {
    alt((
        system_tf_call_list_of_arguments,
        system_tf_call_data_type,
        system_tf_call_clocking_event,
    ))(s)
}

pub fn system_tf_call_list_of_arguments(s: &str) -> IResult<&str, SystemTfCall> {
    let (s, x) = system_tf_identifier(s)?;
    let (s, y) = opt(paren(list_of_arguments))(s)?;
    Ok((
        s,
        SystemTfCall {
            identifier: x,
            argument: y,
            data_type: None,
            expression: None,
            clocking_event: None,
        },
    ))
}

pub fn system_tf_call_data_type(s: &str) -> IResult<&str, SystemTfCall> {
    let (s, x) = system_tf_identifier(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, y) = data_type(s)?;
    let (s, z) = preceded(symbol(","), expression)(s)?;
    let (s, _) = symbol(")")(s)?;
    Ok((
        s,
        SystemTfCall {
            identifier: x,
            argument: None,
            data_type: Some(y),
            expression: Some(vec![z]),
            clocking_event: None,
        },
    ))
}

pub fn system_tf_call_clocking_event(s: &str) -> IResult<&str, SystemTfCall> {
    let (s, x) = system_tf_identifier(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, y) = separated_nonempty_list(symbol(","), expression)(s)?;
    let (s, z) = opt(preceded(symbol(","), opt(clocking_event)))(s)?;
    let (s, _) = symbol(")")(s)?;
    let z = if let Some(Some(z)) = z { Some(z) } else { None };
    Ok((
        s,
        SystemTfCall {
            identifier: x,
            argument: None,
            data_type: None,
            expression: Some(y),
            clocking_event: z,
        },
    ))
}

pub fn subroutine_call(s: &str) -> IResult<&str, SubroutineCall> {
    alt((
        map(tf_call, |x| SubroutineCall::Tf(Box::new(x))),
        map(system_tf_call, |x| SubroutineCall::SystemTf(Box::new(x))),
        map(method_call, |x| SubroutineCall::Method(Box::new(x))),
        map(
            tuple((symbol("std"), symbol("::"), randomize_call)),
            |(_, _, x)| SubroutineCall::StdRandomize(Box::new(x)),
        ),
        map(randomize_call, |x| SubroutineCall::Randomize(Box::new(x))),
    ))(s)
}

pub fn function_subroutine_call(s: &str) -> IResult<&str, SubroutineCall> {
    subroutine_call(s)
}

pub fn list_of_arguments(s: &str) -> IResult<&str, ListOfArguments> {
    let (s, x) = separated_list(symbol(","), expression)(s)?;
    let (s, y) = separated_list(
        symbol(","),
        pair(preceded(symbol("."), identifier), paren(opt(expression))),
    )(s)?;
    Ok((
        s,
        ListOfArguments {
            unnamed: x,
            named: y,
        },
    ))
}

pub fn method_call(s: &str) -> IResult<&str, MethodCall> {
    let (s, x) = method_call_root(s)?;
    let (s, _) = symbol(".")(s)?;
    let (s, y) = method_call_body(s)?;

    Ok((s, MethodCall { root: x, body: y }))
}

pub fn method_call_body(s: &str) -> IResult<&str, MethodCallBody> {
    alt((method_call_body_user, built_in_method_call))(s)
}

pub fn method_call_body_user(s: &str) -> IResult<&str, MethodCallBody> {
    let (s, x) = method_identifier(s)?;
    let (s, y) = many0(attribute_instance)(s)?;
    let (s, z) = opt(paren(list_of_arguments))(s)?;
    Ok((
        s,
        MethodCallBody::User(MethodCallBodyUser {
            identifier: x,
            attribute: y,
            argument: z,
        }),
    ))
}

pub fn built_in_method_call(s: &str) -> IResult<&str, MethodCallBody> {
    alt((
        map(array_manipulation_call, |x| MethodCallBody::Array(x)),
        map(randomize_call, |x| MethodCallBody::Randomize(x)),
    ))(s)
}

pub fn array_manipulation_call(s: &str) -> IResult<&str, ArrayManipulationCall> {
    let (s, x) = array_method_name(s)?;
    let (s, y) = many0(attribute_instance)(s)?;
    let (s, z) = opt(paren(list_of_arguments))(s)?;
    let (s, w) = opt(preceded(symbol("with"), paren(expression)))(s)?;
    Ok((
        s,
        ArrayManipulationCall {
            name: x,
            attribute: y,
            argument: z,
            with: w,
        },
    ))
}

pub fn randomize_call(s: &str) -> IResult<&str, RandomizeCall> {
    let (s, _) = symbol("randomize")(s)?;
    let (s, x) = many0(attribute_instance)(s)?;
    let (s, y) = opt(paren(opt(alt((
        variable_identifier_list,
        map(symbol("null"), |_| vec![]),
    )))))(s)?;
    let (s, z) = opt(tuple((
        symbol("with"),
        opt(paren(opt(identifier_list))),
        constraint_block,
    )))(s)?;
    let y = if let Some(Some(y)) = y { y } else { vec![] };
    let (z, w) = if let Some((_, Some(Some(z)), w)) = z {
        (z, Some(w))
    } else {
        (vec![], None)
    };
    Ok((
        s,
        RandomizeCall {
            attribute: x,
            argument: y,
            with: z,
            constraint_block: w,
        },
    ))
}

pub fn method_call_root(s: &str) -> IResult<&str, MethodCallRoot> {
    alt((
        map(primary, |x| MethodCallRoot::Primary(x)),
        map(implicit_class_handle, |x| {
            MethodCallRoot::ImplicitClassHandle(x)
        }),
    ))(s)
}

pub fn array_method_name(s: &str) -> IResult<&str, ArrayMethodName> {
    alt((
        map(symbol("unique"), |_| ArrayMethodName::Unique),
        map(symbol("and"), |_| ArrayMethodName::And),
        map(symbol("or"), |_| ArrayMethodName::Or),
        map(symbol("xor"), |_| ArrayMethodName::Xor),
        map(method_identifier, |x| ArrayMethodName::Identifier(x)),
    ))(s)
}

// -----------------------------------------------------------------------------
