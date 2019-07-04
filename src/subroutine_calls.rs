use crate::attributes::*;
use crate::expressions::*;
use crate::identifiers::*;
use crate::primaries::*;
use crate::utils::*;
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
    let (s, identifier) = ps_or_hierarchical_tf_identifier(s)?;
    let (s, attribute) = many0(attribute_instance)(s)?;
    let (s, argument) = opt(delimited(symbol("("), list_of_arguments, symbol(")")))(s)?;
    Ok((
        s,
        TfCall {
            identifier,
            attribute,
            argument,
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
    let (s, identifier) = system_tf_identifier(s)?;
    let (s, argument) = opt(delimited(symbol("("), list_of_arguments, symbol(")")))(s)?;
    Ok((
        s,
        SystemTfCall {
            identifier,
            argument,
            data_type: None,
            expression: None,
            clocking_event: None,
        },
    ))
}

pub fn system_tf_call_data_type(s: &str) -> IResult<&str, SystemTfCall> {
    let (s, identifier) = system_tf_identifier(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, data_type) = data_type(s)?;
    let (s, expression) = preceded(symbol(","), expression)(s)?;
    let (s, _) = symbol(")")(s)?;
    let data_type = Some(data_type);
    let expression = Some(vec![expression]);
    Ok((
        s,
        SystemTfCall {
            identifier,
            argument: None,
            data_type,
            expression,
            clocking_event: None,
        },
    ))
}

pub fn system_tf_call_clocking_event(s: &str) -> IResult<&str, SystemTfCall> {
    let (s, identifier) = system_tf_identifier(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, expression) = separated_nonempty_list(symbol(","), expression)(s)?;
    let (s, clocking_event) = opt(preceded(symbol(","), opt(clocking_event)))(s)?;
    let (s, _) = symbol(")")(s)?;
    let expression = Some(expression);
    let clocking_event = if let Some(Some(x)) = clocking_event {
        Some(x)
    } else {
        None
    };
    Ok((
        s,
        SystemTfCall {
            identifier,
            argument: None,
            data_type: None,
            expression,
            clocking_event,
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
    let (s, unnamed) = separated_list(symbol(","), expression)(s)?;
    let (s, named) = separated_list(
        symbol(","),
        pair(
            preceded(symbol("."), identifier),
            delimited(symbol("("), opt(expression), symbol(")")),
        ),
    )(s)?;
    Ok((s, ListOfArguments { unnamed, named }))
}

pub fn method_call(s: &str) -> IResult<&str, MethodCall> {
    let (s, root) = method_call_root(s)?;
    let (s, _) = symbol(".")(s)?;
    let (s, body) = method_call_body(s)?;

    Ok((s, MethodCall { root, body }))
}

pub fn method_call_body(s: &str) -> IResult<&str, MethodCallBody> {
    alt((method_call_body_user, built_in_method_call))(s)
}

pub fn method_call_body_user(s: &str) -> IResult<&str, MethodCallBody> {
    let (s, identifier) = method_identifier(s)?;
    let (s, attribute) = many0(attribute_instance)(s)?;
    let (s, argument) = opt(delimited(symbol("("), list_of_arguments, symbol(")")))(s)?;
    Ok((
        s,
        MethodCallBody::User(MethodCallBodyUser {
            identifier,
            attribute,
            argument,
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
    let (s, name) = array_method_name(s)?;
    let (s, attribute) = many0(attribute_instance)(s)?;
    let (s, argument) = opt(delimited(symbol("("), list_of_arguments, symbol(")")))(s)?;
    let (s, with) = opt(preceded(
        symbol("with"),
        delimited(symbol("("), expression, symbol(")")),
    ))(s)?;
    Ok((
        s,
        ArrayManipulationCall {
            name,
            attribute,
            argument,
            with,
        },
    ))
}

pub fn randomize_call(s: &str) -> IResult<&str, RandomizeCall> {
    let (s, _) = symbol("randomize")(s)?;
    let (s, attribute) = many0(attribute_instance)(s)?;
    let (s, argument) = opt(delimited(
        symbol("("),
        opt(alt((
            variable_identifier_list,
            map(symbol("null"), |_| vec![]),
        ))),
        symbol(")"),
    ))(s)?;
    let (s, with) = opt(tuple((
        symbol("with"),
        opt(delimited(symbol("("), opt(identifier_list), symbol(")"))),
        constraint_block,
    )))(s)?;
    let argument = if let Some(Some(x)) = argument {
        x
    } else {
        vec![]
    };
    let (with, constraint_block) = if let Some((_, Some(Some(x)), y)) = with {
        (x, Some(y))
    } else {
        (vec![], None)
    };
    Ok((
        s,
        RandomizeCall {
            attribute,
            argument,
            with,
            constraint_block,
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
