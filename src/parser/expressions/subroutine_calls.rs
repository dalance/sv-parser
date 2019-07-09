use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct TfCall<'a> {
    pub nodes: (
        PsOrHierarchicalTfIdentifier<'a>,
        Vec<AttributeInstance<'a>>,
        Option<ListOfArguments<'a>>,
    ),
}

#[derive(Debug)]
pub struct SystemTfCall<'a> {
    pub nodes: (
        SystemTfIdentifier<'a>,
        Option<ListOfArguments<'a>>,
        Option<DataType<'a>>,
        Option<Vec<Expression<'a>>>,
        Option<ClockingEvent<'a>>,
    ),
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
    pub nodes: (
        Vec<Expression<'a>>,
        Vec<(Identifier<'a>, Option<Expression<'a>>)>,
    ),
}

#[derive(Debug)]
pub struct MethodCall<'a> {
    pub nodes: (MethodCallRoot<'a>, MethodCallBody<'a>),
}

#[derive(Debug)]
pub enum MethodCallRoot<'a> {
    Primary(Primary<'a>),
    ImplicitClassHandle(ImplicitClassHandle),
}

#[derive(Debug)]
pub enum MethodCallBody<'a> {
    User(MethodCallBodyUser<'a>),
    Array(ArrayManipulationCall<'a>),
    Randomize(RandomizeCall<'a>),
}

#[derive(Debug)]
pub struct MethodCallBodyUser<'a> {
    pub nodes: (
        MethodIdentifier<'a>,
        Vec<AttributeInstance<'a>>,
        Option<ListOfArguments<'a>>,
    ),
}

#[derive(Debug)]
pub struct ArrayManipulationCall<'a> {
    pub nodes: (
        ArrayMethodName<'a>,
        Vec<AttributeInstance<'a>>,
        Option<ListOfArguments<'a>>,
        Option<Expression<'a>>,
    ),
}

#[derive(Debug)]
pub struct RandomizeCall<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        VariableIdentifierList<'a>,
        IdentifierList<'a>,
        Option<ConstraintBlock<'a>>,
    ),
}

#[derive(Debug)]
pub enum ArrayMethodName<'a> {
    MethodIdentifier(MethodIdentifier<'a>),
    Unique,
    And,
    Or,
    Xor,
}

// -----------------------------------------------------------------------------

pub fn constant_function_call(s: Span) -> IResult<Span, SubroutineCall> {
    function_subroutine_call(s)
}

pub fn tf_call(s: Span) -> IResult<Span, TfCall> {
    let (s, x) = ps_or_hierarchical_tf_identifier(s)?;
    let (s, y) = many0(attribute_instance)(s)?;
    let (s, z) = opt(paren(list_of_arguments))(s)?;
    Ok((s, TfCall { nodes: (x, y, z) }))
}

pub fn system_tf_call(s: Span) -> IResult<Span, SystemTfCall> {
    alt((
        system_tf_call_list_of_arguments,
        system_tf_call_data_type,
        system_tf_call_clocking_event,
    ))(s)
}

pub fn system_tf_call_list_of_arguments(s: Span) -> IResult<Span, SystemTfCall> {
    let (s, x) = system_tf_identifier(s)?;
    let (s, y) = opt(paren(list_of_arguments))(s)?;
    Ok((
        s,
        SystemTfCall {
            nodes: (x, y, None, None, None),
        },
    ))
}

pub fn system_tf_call_data_type(s: Span) -> IResult<Span, SystemTfCall> {
    let (s, x) = system_tf_identifier(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, y) = data_type(s)?;
    let (s, z) = preceded(symbol(","), expression)(s)?;
    let (s, _) = symbol(")")(s)?;
    Ok((
        s,
        SystemTfCall {
            nodes: (x, None, Some(y), Some(vec![z]), None),
        },
    ))
}

pub fn system_tf_call_clocking_event(s: Span) -> IResult<Span, SystemTfCall> {
    let (s, x) = system_tf_identifier(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, y) = separated_nonempty_list(symbol(","), expression)(s)?;
    let (s, z) = opt(preceded(symbol(","), opt(clocking_event)))(s)?;
    let (s, _) = symbol(")")(s)?;
    let z = if let Some(Some(z)) = z { Some(z) } else { None };
    Ok((
        s,
        SystemTfCall {
            nodes: (x, None, None, Some(y), z),
        },
    ))
}

pub fn subroutine_call(s: Span) -> IResult<Span, SubroutineCall> {
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

pub fn function_subroutine_call(s: Span) -> IResult<Span, SubroutineCall> {
    subroutine_call(s)
}

pub fn list_of_arguments(s: Span) -> IResult<Span, ListOfArguments> {
    let (s, x) = separated_list(symbol(","), expression)(s)?;
    let (s, y) = separated_list(
        symbol(","),
        pair(preceded(symbol("."), identifier), paren(opt(expression))),
    )(s)?;
    Ok((s, ListOfArguments { nodes: (x, y) }))
}

pub fn method_call(s: Span) -> IResult<Span, MethodCall> {
    let (s, x) = method_call_root(s)?;
    let (s, _) = symbol(".")(s)?;
    let (s, y) = method_call_body(s)?;

    Ok((s, MethodCall { nodes: (x, y) }))
}

pub fn method_call_body(s: Span) -> IResult<Span, MethodCallBody> {
    alt((method_call_body_user, built_in_method_call))(s)
}

pub fn method_call_body_user(s: Span) -> IResult<Span, MethodCallBody> {
    let (s, x) = method_identifier(s)?;
    let (s, y) = many0(attribute_instance)(s)?;
    let (s, z) = opt(paren(list_of_arguments))(s)?;
    Ok((
        s,
        MethodCallBody::User(MethodCallBodyUser { nodes: (x, y, z) }),
    ))
}

pub fn built_in_method_call(s: Span) -> IResult<Span, MethodCallBody> {
    alt((
        map(array_manipulation_call, |x| MethodCallBody::Array(x)),
        map(randomize_call, |x| MethodCallBody::Randomize(x)),
    ))(s)
}

pub fn array_manipulation_call(s: Span) -> IResult<Span, ArrayManipulationCall> {
    let (s, x) = array_method_name(s)?;
    let (s, y) = many0(attribute_instance)(s)?;
    let (s, z) = opt(paren(list_of_arguments))(s)?;
    let (s, v) = opt(preceded(symbol("with"), paren(expression)))(s)?;
    Ok((
        s,
        ArrayManipulationCall {
            nodes: (x, y, z, v),
        },
    ))
}

pub fn randomize_call(s: Span) -> IResult<Span, RandomizeCall> {
    let (s, _) = symbol("randomize")(s)?;
    let (s, x) = many0(attribute_instance)(s)?;
    let (s, y) = opt(paren(opt(alt((
        variable_identifier_list,
        map(symbol("null"), |_| VariableIdentifierList {
            nodes: (vec![],),
        }),
    )))))(s)?;
    let (s, z) = opt(tuple((
        symbol("with"),
        opt(paren(opt(identifier_list))),
        constraint_block,
    )))(s)?;
    let y = if let Some(Some(y)) = y {
        y
    } else {
        VariableIdentifierList { nodes: (vec![],) }
    };
    let (z, v) = if let Some((_, Some(Some(z)), v)) = z {
        (z, Some(v))
    } else {
        (IdentifierList { nodes: (vec![],) }, None)
    };
    Ok((
        s,
        RandomizeCall {
            nodes: (x, y, z, v),
        },
    ))
}

pub fn method_call_root(s: Span) -> IResult<Span, MethodCallRoot> {
    alt((
        map(primary, |x| MethodCallRoot::Primary(x)),
        map(implicit_class_handle, |x| {
            MethodCallRoot::ImplicitClassHandle(x)
        }),
    ))(s)
}

pub fn array_method_name(s: Span) -> IResult<Span, ArrayMethodName> {
    alt((
        map(symbol("unique"), |_| ArrayMethodName::Unique),
        map(symbol("and"), |_| ArrayMethodName::And),
        map(symbol("or"), |_| ArrayMethodName::Or),
        map(symbol("xor"), |_| ArrayMethodName::Xor),
        map(method_identifier, |x| ArrayMethodName::MethodIdentifier(x)),
    ))(s)
}

// -----------------------------------------------------------------------------
