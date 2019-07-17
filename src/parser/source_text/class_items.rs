use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum ClassItem<'a> {
    Property(ClassItemProperty<'a>),
    Method(ClassItemMethod<'a>),
    Constraint(ClassItemConstraint<'a>),
    Declaration(ClassItemDeclaration<'a>),
    Covergroup(ClassItemCovergroup<'a>),
    LocalParameterDeclaration((LocalParameterDeclaration<'a>, Symbol<'a>)),
    ParameterDeclaration((ParameterDeclaration<'a>, Symbol<'a>)),
    Empty(Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct ClassItemProperty<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ClassProperty<'a>),
}

#[derive(Debug, Node)]
pub struct ClassItemMethod<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ClassMethod<'a>),
}

#[derive(Debug, Node)]
pub struct ClassItemConstraint<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ClassConstraint<'a>),
}

#[derive(Debug, Node)]
pub struct ClassItemDeclaration<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ClassDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct ClassItemCovergroup<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, CovergroupDeclaration<'a>),
}

#[derive(Debug, Node)]
pub enum ClassProperty<'a> {
    NonConst(ClassPropertyNonConst<'a>),
    Const(ClassPropertyConst<'a>),
}

#[derive(Debug, Node)]
pub struct ClassPropertyNonConst<'a> {
    pub nodes: (Vec<PropertyQualifier<'a>>, DataDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct ClassPropertyConst<'a> {
    pub nodes: (
        Symbol<'a>,
        Vec<ClassItemQualifier<'a>>,
        DataType<'a>,
        ConstIdentifier<'a>,
        Option<(Symbol<'a>, ConstantExpression<'a>)>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum ClassMethod<'a> {
    Task(ClassMethodTask<'a>),
    Function(ClassMethodFunction<'a>),
    PureVirtual(ClassMethodPureVirtual<'a>),
    ExternMethod(ClassMethodExternMethod<'a>),
    Constructor(ClassMethodConstructor<'a>),
    ExternConstructor(ClassMethodExternConstructor<'a>),
}

#[derive(Debug, Node)]
pub struct ClassMethodTask<'a> {
    pub nodes: (Vec<MethodQualifier<'a>>, TaskDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct ClassMethodFunction<'a> {
    pub nodes: (Vec<MethodQualifier<'a>>, FunctionDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct ClassMethodPureVirtual<'a> {
    pub nodes: (
        Symbol<'a>,
        Symbol<'a>,
        Vec<ClassItemQualifier<'a>>,
        MethodPrototype<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ClassMethodExternMethod<'a> {
    pub nodes: (
        Symbol<'a>,
        Vec<MethodQualifier<'a>>,
        MethodPrototype<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ClassMethodConstructor<'a> {
    pub nodes: (Vec<MethodQualifier<'a>>, ClassConstructorDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct ClassMethodExternConstructor<'a> {
    pub nodes: (
        Symbol<'a>,
        Vec<MethodQualifier<'a>>,
        ClassConstructorPrototype<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ClassConstructorPrototype<'a> {
    pub nodes: (
        Symbol<'a>,
        Symbol<'a>,
        Option<Paren<'a, Option<TfPortList<'a>>>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum ClassConstraint<'a> {
    ConstraintPrototype(ConstraintPrototype<'a>),
    ConstraintDeclaration(ConstraintDeclaration<'a>),
}

#[derive(Debug, Node)]
pub enum ClassItemQualifier<'a> {
    Static(Symbol<'a>),
    Protected(Symbol<'a>),
    Local(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum PropertyQualifier<'a> {
    RandomQualifier(RandomQualifier<'a>),
    ClassItemQualifier(ClassItemQualifier<'a>),
}

#[derive(Debug, Node)]
pub enum RandomQualifier<'a> {
    Rand(Symbol<'a>),
    Randc(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum MethodQualifier<'a> {
    Virtual(Symbol<'a>),
    PureVirtual((Symbol<'a>, Symbol<'a>)),
    ClassItemQualifier(ClassItemQualifier<'a>),
}

#[derive(Debug, Node)]
pub enum MethodPrototype<'a> {
    TaskPrototype(TaskPrototype<'a>),
    FunctionPrototype(FunctionPrototype<'a>),
}

#[derive(Debug, Node)]
pub struct ClassConstructorDeclaration<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<ClassScope<'a>>,
        Symbol<'a>,
        Option<Paren<'a, Option<TfPortList<'a>>>>,
        Symbol<'a>,
        Vec<BlockItemDeclaration<'a>>,
        Option<(
            Symbol<'a>,
            Symbol<'a>,
            Symbol<'a>,
            Option<Paren<'a, ListOfArguments<'a>>>,
            Symbol<'a>,
        )>,
        Vec<FunctionStatementOrNull<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, New<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct New<'a> {
    pub nodes: (Symbol<'a>,),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn class_item(s: Span) -> IResult<Span, ClassItem> {
    alt((
        class_item_property,
        class_item_method,
        class_item_constraint,
        class_item_declaration,
        class_item_covergroup,
        map(pair(local_parameter_declaration, symbol(";")), |x| {
            ClassItem::LocalParameterDeclaration(x)
        }),
        map(pair(parameter_declaration, symbol(";")), |x| {
            ClassItem::ParameterDeclaration(x)
        }),
        map(symbol(";"), |x| ClassItem::Empty(x)),
    ))(s)
}

#[parser]
pub fn class_item_property(s: Span) -> IResult<Span, ClassItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = class_property(s)?;
    Ok((s, ClassItem::Property(ClassItemProperty { nodes: (a, b) })))
}

#[parser]
pub fn class_item_method(s: Span) -> IResult<Span, ClassItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = class_method(s)?;
    Ok((s, ClassItem::Method(ClassItemMethod { nodes: (a, b) })))
}

#[parser]
pub fn class_item_constraint(s: Span) -> IResult<Span, ClassItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = class_constraint(s)?;
    Ok((
        s,
        ClassItem::Constraint(ClassItemConstraint { nodes: (a, b) }),
    ))
}

#[parser]
pub fn class_item_declaration(s: Span) -> IResult<Span, ClassItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = class_declaration(s)?;
    Ok((
        s,
        ClassItem::Declaration(ClassItemDeclaration { nodes: (a, b) }),
    ))
}

#[parser]
pub fn class_item_covergroup(s: Span) -> IResult<Span, ClassItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = covergroup_declaration(s)?;
    Ok((
        s,
        ClassItem::Covergroup(ClassItemCovergroup { nodes: (a, b) }),
    ))
}

#[parser]
pub fn class_property(s: Span) -> IResult<Span, ClassProperty> {
    alt((class_property_non_const, class_property_const))(s)
}

#[parser]
pub fn class_property_non_const(s: Span) -> IResult<Span, ClassProperty> {
    let (s, a) = many0(property_qualifier)(s)?;
    let (s, b) = data_declaration(s)?;
    Ok((
        s,
        ClassProperty::NonConst(ClassPropertyNonConst { nodes: (a, b) }),
    ))
}

#[parser]
pub fn class_property_const(s: Span) -> IResult<Span, ClassProperty> {
    let (s, a) = symbol("const")(s)?;
    let (s, b) = many0(class_item_qualifier)(s)?;
    let (s, c) = data_type(s)?;
    let (s, d) = const_identifier(s)?;
    let (s, e) = opt(pair(symbol("="), constant_expression))(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        ClassProperty::Const(ClassPropertyConst {
            nodes: (a, b, c, d, e, f),
        }),
    ))
}

#[parser]
pub fn class_method(s: Span) -> IResult<Span, ClassMethod> {
    alt((
        class_method_task,
        class_method_function,
        class_method_pure_virtual,
        class_method_extern_method,
        class_method_constructor,
        class_method_extern_constructor,
    ))(s)
}

#[parser]
pub fn class_method_task(s: Span) -> IResult<Span, ClassMethod> {
    let (s, a) = many0(method_qualifier)(s)?;
    let (s, b) = task_declaration(s)?;
    Ok((s, ClassMethod::Task(ClassMethodTask { nodes: (a, b) })))
}

#[parser]
pub fn class_method_function(s: Span) -> IResult<Span, ClassMethod> {
    let (s, a) = many0(method_qualifier)(s)?;
    let (s, b) = function_declaration(s)?;
    Ok((
        s,
        ClassMethod::Function(ClassMethodFunction { nodes: (a, b) }),
    ))
}

#[parser]
pub fn class_method_pure_virtual(s: Span) -> IResult<Span, ClassMethod> {
    let (s, a) = symbol("pure")(s)?;
    let (s, b) = symbol("virtual")(s)?;
    let (s, c) = many0(class_item_qualifier)(s)?;
    let (s, d) = method_prototype(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        ClassMethod::PureVirtual(ClassMethodPureVirtual {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn class_method_extern_method(s: Span) -> IResult<Span, ClassMethod> {
    let (s, a) = symbol("extern")(s)?;
    let (s, b) = many0(method_qualifier)(s)?;
    let (s, c) = method_prototype(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        ClassMethod::ExternMethod(ClassMethodExternMethod {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn class_method_constructor(s: Span) -> IResult<Span, ClassMethod> {
    let (s, a) = many0(method_qualifier)(s)?;
    let (s, b) = class_constructor_declaration(s)?;
    Ok((
        s,
        ClassMethod::Constructor(ClassMethodConstructor { nodes: (a, b) }),
    ))
}

#[parser]
pub fn class_method_extern_constructor(s: Span) -> IResult<Span, ClassMethod> {
    let (s, a) = symbol("extern")(s)?;
    let (s, b) = many0(method_qualifier)(s)?;
    let (s, c) = class_constructor_prototype(s)?;
    Ok((
        s,
        ClassMethod::ExternConstructor(ClassMethodExternConstructor { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn class_constructor_prototype(s: Span) -> IResult<Span, ClassConstructorPrototype> {
    let (s, a) = symbol("function")(s)?;
    let (s, b) = symbol("new")(s)?;
    let (s, c) = opt(paren(opt(tf_port_list)))(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        ClassConstructorPrototype {
            nodes: (a, b, c, d),
        },
    ))
}

#[parser]
pub fn class_constraint(s: Span) -> IResult<Span, ClassConstraint> {
    alt((
        map(constraint_prototype, |x| {
            ClassConstraint::ConstraintPrototype(x)
        }),
        map(constraint_declaration, |x| {
            ClassConstraint::ConstraintDeclaration(x)
        }),
    ))(s)
}

#[parser]
pub fn class_item_qualifier(s: Span) -> IResult<Span, ClassItemQualifier> {
    alt((
        map(symbol("static"), |x| ClassItemQualifier::Static(x)),
        map(symbol("protected"), |x| ClassItemQualifier::Protected(x)),
        map(symbol("local"), |x| ClassItemQualifier::Local(x)),
    ))(s)
}

#[parser]
pub fn property_qualifier(s: Span) -> IResult<Span, PropertyQualifier> {
    alt((
        map(random_qualifier, |x| PropertyQualifier::RandomQualifier(x)),
        map(class_item_qualifier, |x| {
            PropertyQualifier::ClassItemQualifier(x)
        }),
    ))(s)
}

#[parser]
pub fn random_qualifier(s: Span) -> IResult<Span, RandomQualifier> {
    alt((
        map(symbol("randc"), |x| RandomQualifier::Randc(x)),
        map(symbol("rand"), |x| RandomQualifier::Rand(x)),
    ))(s)
}

#[parser]
pub fn method_qualifier(s: Span) -> IResult<Span, MethodQualifier> {
    alt((
        map(pair(symbol("pure"), symbol("virtual")), |x| {
            MethodQualifier::PureVirtual(x)
        }),
        map(symbol("virtual"), |x| MethodQualifier::Virtual(x)),
        map(class_item_qualifier, |x| {
            MethodQualifier::ClassItemQualifier(x)
        }),
    ))(s)
}

#[parser]
pub fn method_prototype(s: Span) -> IResult<Span, MethodPrototype> {
    alt((
        map(task_prototype, |x| MethodPrototype::TaskPrototype(x)),
        map(function_prototype, |x| {
            MethodPrototype::FunctionPrototype(x)
        }),
    ))(s)
}

#[parser]
pub fn class_constructor_declaration(s: Span) -> IResult<Span, ClassConstructorDeclaration> {
    let (s, a) = symbol("function")(s)?;
    let (s, b) = opt(class_scope)(s)?;
    let (s, c) = symbol("new")(s)?;
    let (s, d) = opt(paren(opt(tf_port_list)))(s)?;
    let (s, e) = symbol(";")(s)?;
    let (s, f) = many0(block_item_declaration)(s)?;
    let (s, g) = opt(tuple((
        symbol("super"),
        symbol("."),
        symbol("new"),
        opt(paren(list_of_arguments)),
        symbol(";"),
    )))(s)?;
    let (s, h) = many0(function_statement_or_null)(s)?;
    let (s, i) = symbol("end")(s)?;
    let (s, j) = opt(pair(symbol(":"), new))(s)?;
    Ok((
        s,
        ClassConstructorDeclaration {
            nodes: (a, b, c, d, e, f, g, h, i, j),
        },
    ))
}

#[parser]
pub fn new(s: Span) -> IResult<Span, New> {
    let (s, a) = symbol("new")(s)?;
    Ok((s, New { nodes: (a,) }))
}
