use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct TaskDeclaration<'a> {
    pub nodes: (Symbol<'a>, Option<Lifetime<'a>>, TaskBodyDeclaration<'a>),
}

#[derive(Debug, Node)]
pub enum TaskBodyDeclaration<'a> {
    WithoutPort(TaskBodyDeclarationWithoutPort<'a>),
    WithPort(TaskBodyDeclarationWithPort<'a>),
}

#[derive(Debug, Node)]
pub struct TaskBodyDeclarationWithoutPort<'a> {
    pub nodes: (
        Option<InterfaceIdentifierOrClassScope<'a>>,
        TaskIdentifier<'a>,
        Symbol<'a>,
        Vec<TfItemDeclaration<'a>>,
        Vec<StatementOrNull<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, TaskIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct TaskBodyDeclarationWithPort<'a> {
    pub nodes: (
        Option<InterfaceIdentifierOrClassScope<'a>>,
        TaskIdentifier<'a>,
        Paren<'a, Option<TfPortList<'a>>>,
        Symbol<'a>,
        Vec<BlockItemDeclaration<'a>>,
        Vec<StatementOrNull<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, TaskIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub enum TfItemDeclaration<'a> {
    BlockItemDeclaration(BlockItemDeclaration<'a>),
    TfPortDeclaration(TfPortDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct TfPortList<'a> {
    pub nodes: (List<Symbol<'a>, TfPortItem<'a>>,),
}

#[derive(Debug, Node)]
pub struct TfPortItem<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Option<TfPortDirection<'a>>,
        Option<Var<'a>>,
        DataTypeOrImplicit<'a>,
        Option<(
            PortIdentifier<'a>,
            Vec<VariableDimension<'a>>,
            Option<(Symbol<'a>, Expression<'a>)>,
        )>,
    ),
}

#[derive(Debug, Node)]
pub enum TfPortDirection<'a> {
    PortDirection(PortDirection<'a>),
    ConstRef((Symbol<'a>, Symbol<'a>)),
}

#[derive(Debug, Node)]
pub struct TfPortDeclaration<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        TfPortDirection<'a>,
        Option<Var<'a>>,
        DataTypeOrImplicit<'a>,
        ListOfTfVariableIdentifiers<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct TaskPrototype<'a> {
    pub nodes: (
        Symbol<'a>,
        TaskIdentifier<'a>,
        Option<Paren<'a, Option<TfPortList<'a>>>>,
    ),
}

// -----------------------------------------------------------------------------

#[trace]
pub fn task_declaration(s: Span) -> IResult<Span, TaskDeclaration> {
    let (s, a) = symbol("task")(s)?;
    let (s, b) = opt(lifetime)(s)?;
    let (s, c) = task_body_declaration(s)?;
    Ok((s, TaskDeclaration { nodes: (a, b, c) }))
}

#[trace]
pub fn task_body_declaration(s: Span) -> IResult<Span, TaskBodyDeclaration> {
    alt((
        task_body_declaration_without_port,
        task_body_declaration_with_port,
    ))(s)
}

#[trace]
pub fn task_body_declaration_without_port(s: Span) -> IResult<Span, TaskBodyDeclaration> {
    let (s, a) = opt(interface_identifier_or_class_scope)(s)?;
    let (s, b) = task_identifier(s)?;
    let (s, c) = symbol(";")(s)?;
    let (s, d) = many0(tf_item_declaration)(s)?;
    let (s, e) = many0(statement_or_null)(s)?;
    let (s, f) = symbol("endtask")(s)?;
    let (s, g) = opt(pair(symbol(":"), task_identifier))(s)?;
    Ok((
        s,
        TaskBodyDeclaration::WithoutPort(TaskBodyDeclarationWithoutPort {
            nodes: (a, b, c, d, e, f, g),
        }),
    ))
}

#[trace]
pub fn task_body_declaration_with_port(s: Span) -> IResult<Span, TaskBodyDeclaration> {
    let (s, a) = opt(interface_identifier_or_class_scope)(s)?;
    let (s, b) = task_identifier(s)?;
    let (s, c) = paren(opt(tf_port_list))(s)?;
    let (s, d) = symbol(";")(s)?;
    let (s, e) = many0(block_item_declaration)(s)?;
    let (s, f) = many0(statement_or_null)(s)?;
    let (s, g) = symbol("endtask")(s)?;
    let (s, h) = opt(pair(symbol(":"), task_identifier))(s)?;
    Ok((
        s,
        TaskBodyDeclaration::WithPort(TaskBodyDeclarationWithPort {
            nodes: (a, b, c, d, e, f, g, h),
        }),
    ))
}

#[trace]
pub fn tf_item_declaration(s: Span) -> IResult<Span, TfItemDeclaration> {
    alt((
        map(block_item_declaration, |x| {
            TfItemDeclaration::BlockItemDeclaration(x)
        }),
        map(tf_port_declaration, |x| {
            TfItemDeclaration::TfPortDeclaration(x)
        }),
    ))(s)
}

#[trace]
pub fn tf_port_list(s: Span) -> IResult<Span, TfPortList> {
    let (s, a) = list(symbol(","), tf_port_item)(s)?;
    Ok((s, TfPortList { nodes: (a,) }))
}

#[trace]
pub fn tf_port_item(s: Span) -> IResult<Span, TfPortItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = opt(tf_port_direction)(s)?;
    let (s, c) = opt(var)(s)?;
    let (s, d) = data_type_or_implicit(s)?;
    let (s, e) = opt(triple(
        port_identifier,
        many0(variable_dimension),
        opt(pair(symbol(":"), expression)),
    ))(s)?;
    Ok((
        s,
        TfPortItem {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[trace]
pub fn tf_port_direction(s: Span) -> IResult<Span, TfPortDirection> {
    alt((
        map(port_direction, |x| TfPortDirection::PortDirection(x)),
        map(pair(symbol("const"), symbol("ref")), |x| {
            TfPortDirection::ConstRef(x)
        }),
    ))(s)
}

#[trace]
pub fn tf_port_declaration(s: Span) -> IResult<Span, TfPortDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = tf_port_direction(s)?;
    let (s, c) = opt(var)(s)?;
    let (s, d) = data_type_or_implicit(s)?;
    let (s, e) = list_of_tf_variable_identifiers(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        TfPortDeclaration {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

#[trace]
pub fn task_prototype(s: Span) -> IResult<Span, TaskPrototype> {
    let (s, a) = symbol("task")(s)?;
    let (s, b) = task_identifier(s)?;
    let (s, c) = opt(paren(opt(tf_port_list)))(s)?;
    Ok((s, TaskPrototype { nodes: (a, b, c) }))
}
