use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct ConstantFunctionCall<'a> {
    pub nodes: (FunctionSubroutineCall<'a>,),
}

#[derive(Debug)]
pub struct TfCall<'a> {
    pub nodes: (
        PsOrHierarchicalTfIdentifier<'a>,
        Vec<AttributeInstance<'a>>,
        Option<(Symbol<'a>, ListOfArguments<'a>, Symbol<'a>)>,
    ),
}

#[derive(Debug)]
pub enum SystemTfCall<'a> {
    ArgOptionl(SystemTfCallArgOptional<'a>),
    ArgDataType(SystemTfCallArgDataType<'a>),
    ArgExpression(SystemTfCallArgExpression<'a>),
}

#[derive(Debug)]
pub struct SystemTfCallArgOptional<'a> {
    pub nodes: (
        SystemTfIdentifier<'a>,
        Option<(Symbol<'a>, ListOfArguments<'a>, Symbol<'a>)>,
    ),
}

#[derive(Debug)]
pub struct SystemTfCallArgDataType<'a> {
    pub nodes: (
        SystemTfIdentifier<'a>,
        Symbol<'a>,
        DataType<'a>,
        Option<(Symbol<'a>, Expression<'a>)>,
        Symbol<'a>,
    ),
}

#[derive(Debug)]
pub struct SystemTfCallArgExpression<'a> {
    pub nodes: (
        SystemTfIdentifier<'a>,
        Symbol<'a>,
        Expression<'a>,
        Vec<(Symbol<'a>, Option<Expression<'a>>)>,
        Option<(Symbol<'a>, Option<ClockingEvent<'a>>)>,
        Symbol<'a>,
    ),
}

#[derive(Debug)]
pub enum SubroutineCall<'a> {
    TfCall(Box<TfCall<'a>>),
    SystemTfCall(Box<SystemTfCall<'a>>),
    MethodCall(Box<MethodCall<'a>>),
    Randomize(Box<SubroutineCallRandomize<'a>>),
}

#[derive(Debug)]
pub struct SubroutineCallRandomize<'a> {
    pub nodes: (Option<(Symbol<'a>, Symbol<'a>)>, RandomizeCall<'a>),
}

#[derive(Debug)]
pub struct FunctionSubroutineCall<'a> {
    pub nodes: (SubroutineCall<'a>,),
}

#[derive(Debug)]
pub enum ListOfArguments<'a> {
    Ordered(ListOfArgumentsOrdered<'a>),
    Named(ListOfArgumentsNamed<'a>),
}

#[derive(Debug)]
pub struct ListOfArgumentsOrdered<'a> {
    pub nodes: (
        Option<Expression<'a>>,
        Vec<(Symbol<'a>, Option<Expression<'a>>)>,
        Vec<(
            Symbol<'a>,
            Symbol<'a>,
            Identifier<'a>,
            Symbol<'a>,
            Option<Expression<'a>>,
            Symbol<'a>,
        )>,
    ),
}

#[derive(Debug)]
pub struct ListOfArgumentsNamed<'a> {
    pub nodes: (
        Symbol<'a>,
        Identifier<'a>,
        Symbol<'a>,
        Option<Expression<'a>>,
        Symbol<'a>,
        Vec<(
            Symbol<'a>,
            Symbol<'a>,
            Identifier<'a>,
            Symbol<'a>,
            Option<Expression<'a>>,
            Symbol<'a>,
        )>,
    ),
}

#[derive(Debug)]
pub struct MethodCall<'a> {
    pub nodes: (MethodCallRoot<'a>, Symbol<'a>, MethodCallBody<'a>),
}

#[derive(Debug)]
pub enum MethodCallBody<'a> {
    User(MethodCallBodyUser<'a>),
    BuiltInMethodCall(BuiltInMethodCall<'a>),
}

#[derive(Debug)]
pub struct MethodCallBodyUser<'a> {
    pub nodes: (
        MethodIdentifier<'a>,
        Vec<AttributeInstance<'a>>,
        Option<(Symbol<'a>, ListOfArguments<'a>, Symbol<'a>)>,
    ),
}

#[derive(Debug)]
pub enum BuiltInMethodCall<'a> {
    ArrayManipulationCall(ArrayManipulationCall<'a>),
    RandomizeCall(RandomizeCall<'a>),
}

#[derive(Debug)]
pub struct ArrayManipulationCall<'a> {
    pub nodes: (
        ArrayMethodName<'a>,
        Vec<AttributeInstance<'a>>,
        Option<(Symbol<'a>, ListOfArguments<'a>, Symbol<'a>)>,
        Option<(Symbol<'a>, (Symbol<'a>, Expression<'a>, Symbol<'a>))>,
    ),
}

#[derive(Debug)]
pub struct RandomizeCall<'a> {
    pub nodes: (
        Symbol<'a>,
        Vec<AttributeInstance<'a>>,
        Option<(
            Symbol<'a>,
            Option<VariableIdentifierListOrNull<'a>>,
            Symbol<'a>,
        )>,
        Option<(
            Symbol<'a>,
            Option<(Symbol<'a>, Option<IdentifierList<'a>>, Symbol<'a>)>,
            ConstraintBlock<'a>,
        )>,
    ),
}

#[derive(Debug)]
pub enum VariableIdentifierListOrNull<'a> {
    VariableIdentifierList(VariableIdentifierList<'a>),
    Null(Symbol<'a>),
}

#[derive(Debug)]
pub enum MethodCallRoot<'a> {
    Primary(Primary<'a>),
    ImplicitClassHandle(ImplicitClassHandle<'a>),
}

#[derive(Debug)]
pub enum ArrayMethodName<'a> {
    MethodIdentifier(MethodIdentifier<'a>),
    Unique(Symbol<'a>),
    And(Symbol<'a>),
    Or(Symbol<'a>),
    Xor(Symbol<'a>),
}

// -----------------------------------------------------------------------------

pub fn constant_function_call(s: Span) -> IResult<Span, ConstantFunctionCall> {
    let (s, a) = function_subroutine_call(s)?;
    Ok((s, ConstantFunctionCall { nodes: (a,) }))
}

pub fn tf_call(s: Span) -> IResult<Span, TfCall> {
    let (s, a) = ps_or_hierarchical_tf_identifier(s)?;
    let (s, b) = many0(attribute_instance)(s)?;
    let (s, c) = opt(paren2(list_of_arguments))(s)?;
    Ok((s, TfCall { nodes: (a, b, c) }))
}

pub fn system_tf_call(s: Span) -> IResult<Span, SystemTfCall> {
    alt((
        system_tf_call_arg_optional,
        system_tf_call_arg_data_type,
        system_tf_call_arg_expression,
    ))(s)
}

pub fn system_tf_call_arg_optional(s: Span) -> IResult<Span, SystemTfCall> {
    let (s, a) = system_tf_identifier(s)?;
    let (s, b) = opt(paren2(list_of_arguments))(s)?;
    Ok((
        s,
        SystemTfCall::ArgOptionl(SystemTfCallArgOptional { nodes: (a, b) }),
    ))
}

pub fn system_tf_call_arg_data_type(s: Span) -> IResult<Span, SystemTfCall> {
    let (s, a) = system_tf_identifier(s)?;
    let (s, b) = symbol("(")(s)?;
    let (s, c) = data_type(s)?;
    let (s, d) = opt(pair(symbol(","), expression))(s)?;
    let (s, e) = symbol(")")(s)?;
    Ok((
        s,
        SystemTfCall::ArgDataType(SystemTfCallArgDataType {
            nodes: (a, b, c, d, e),
        }),
    ))
}

pub fn system_tf_call_arg_expression(s: Span) -> IResult<Span, SystemTfCall> {
    let (s, a) = system_tf_identifier(s)?;
    let (s, b) = symbol("(")(s)?;
    let (s, c) = expression(s)?;
    let (s, d) = many0(pair(symbol(","), opt(expression)))(s)?;
    let (s, e) = opt(pair(symbol(","), opt(clocking_event)))(s)?;
    let (s, f) = symbol(")")(s)?;
    Ok((
        s,
        SystemTfCall::ArgExpression(SystemTfCallArgExpression {
            nodes: (a, b, c, d, e, f),
        }),
    ))
}

pub fn subroutine_call(s: Span) -> IResult<Span, SubroutineCall> {
    alt((
        map(tf_call, |x| SubroutineCall::TfCall(Box::new(x))),
        map(system_tf_call, |x| {
            SubroutineCall::SystemTfCall(Box::new(x))
        }),
        map(method_call, |x| SubroutineCall::MethodCall(Box::new(x))),
        subroutine_call_randomize,
    ))(s)
}

pub fn subroutine_call_randomize(s: Span) -> IResult<Span, SubroutineCall> {
    let (s, a) = opt(pair(symbol("std"), symbol("::")))(s)?;
    let (s, b) = randomize_call(s)?;
    Ok((
        s,
        SubroutineCall::Randomize(Box::new(SubroutineCallRandomize { nodes: (a, b) })),
    ))
}

pub fn function_subroutine_call(s: Span) -> IResult<Span, FunctionSubroutineCall> {
    map(subroutine_call, |x| FunctionSubroutineCall { nodes: (x,) })(s)
}

pub fn list_of_arguments(s: Span) -> IResult<Span, ListOfArguments> {
    alt((list_of_arguments_ordered, list_of_arguments_named))(s)
}

pub fn list_of_arguments_ordered(s: Span) -> IResult<Span, ListOfArguments> {
    let (s, a) = opt(expression)(s)?;
    let (s, b) = many0(pair(symbol(","), opt(expression)))(s)?;
    let (s, c) = many0(tuple((
        symbol(","),
        symbol("."),
        identifier,
        symbol("("),
        opt(expression),
        symbol(")"),
    )))(s)?;
    Ok((
        s,
        ListOfArguments::Ordered(ListOfArgumentsOrdered { nodes: (a, b, c) }),
    ))
}

pub fn list_of_arguments_named(s: Span) -> IResult<Span, ListOfArguments> {
    let (s, a) = symbol(".")(s)?;
    let (s, b) = identifier(s)?;
    let (s, c) = symbol("(")(s)?;
    let (s, d) = opt(expression)(s)?;
    let (s, e) = symbol(")")(s)?;
    let (s, f) = many0(tuple((
        symbol(","),
        symbol("."),
        identifier,
        symbol("("),
        opt(expression),
        symbol(")"),
    )))(s)?;
    Ok((
        s,
        ListOfArguments::Named(ListOfArgumentsNamed {
            nodes: (a, b, c, d, e, f),
        }),
    ))
}

pub fn method_call(s: Span) -> IResult<Span, MethodCall> {
    let (s, a) = method_call_root(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = method_call_body(s)?;

    Ok((s, MethodCall { nodes: (a, b, c) }))
}

pub fn method_call_body(s: Span) -> IResult<Span, MethodCallBody> {
    alt((
        method_call_body_user,
        map(built_in_method_call, |x| {
            MethodCallBody::BuiltInMethodCall(x)
        }),
    ))(s)
}

pub fn method_call_body_user(s: Span) -> IResult<Span, MethodCallBody> {
    let (s, a) = method_identifier(s)?;
    let (s, b) = many0(attribute_instance)(s)?;
    let (s, c) = opt(paren2(list_of_arguments))(s)?;
    Ok((
        s,
        MethodCallBody::User(MethodCallBodyUser { nodes: (a, b, c) }),
    ))
}

pub fn built_in_method_call(s: Span) -> IResult<Span, BuiltInMethodCall> {
    alt((
        map(array_manipulation_call, |x| {
            BuiltInMethodCall::ArrayManipulationCall(x)
        }),
        map(randomize_call, |x| BuiltInMethodCall::RandomizeCall(x)),
    ))(s)
}

pub fn array_manipulation_call(s: Span) -> IResult<Span, ArrayManipulationCall> {
    let (s, a) = array_method_name(s)?;
    let (s, b) = many0(attribute_instance)(s)?;
    let (s, c) = opt(paren2(list_of_arguments))(s)?;
    let (s, d) = opt(pair(symbol("with"), paren2(expression)))(s)?;
    Ok((
        s,
        ArrayManipulationCall {
            nodes: (a, b, c, d),
        },
    ))
}

pub fn randomize_call(s: Span) -> IResult<Span, RandomizeCall> {
    let (s, a) = symbol("randomize")(s)?;
    let (s, b) = many0(attribute_instance)(s)?;
    let (s, c) = opt(paren2(opt(variable_identifier_list_or_null)))(s)?;
    let (s, d) = opt(triple(
        symbol("with"),
        opt(paren2(opt(identifier_list))),
        constraint_block,
    ))(s)?;
    Ok((
        s,
        RandomizeCall {
            nodes: (a, b, c, d),
        },
    ))
}

pub fn variable_identifier_list_or_null(s: Span) -> IResult<Span, VariableIdentifierListOrNull> {
    alt((
        map(variable_identifier_list, |x| {
            VariableIdentifierListOrNull::VariableIdentifierList(x)
        }),
        map(symbol("null"), |x| VariableIdentifierListOrNull::Null(x)),
    ))(s)
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
        map(symbol("unique"), |x| ArrayMethodName::Unique(x)),
        map(symbol("and"), |x| ArrayMethodName::And(x)),
        map(symbol("or"), |x| ArrayMethodName::Or(x)),
        map(symbol("xor"), |x| ArrayMethodName::Xor(x)),
        map(method_identifier, |x| ArrayMethodName::MethodIdentifier(x)),
    ))(s)
}

// -----------------------------------------------------------------------------
