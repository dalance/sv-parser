use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum ClassItem {
    Property(ClassItemProperty),
    Method(ClassItemMethod),
    Constraint(ClassItemConstraint),
    Declaration(ClassItemDeclaration),
    Covergroup(ClassItemCovergroup),
    LocalParameterDeclaration((LocalParameterDeclaration, Symbol)),
    ParameterDeclaration((ParameterDeclaration, Symbol)),
    Empty(Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct ClassItemProperty {
    pub nodes: (Vec<AttributeInstance>, ClassProperty),
}

#[derive(Clone, Debug, Node)]
pub struct ClassItemMethod {
    pub nodes: (Vec<AttributeInstance>, ClassMethod),
}

#[derive(Clone, Debug, Node)]
pub struct ClassItemConstraint {
    pub nodes: (Vec<AttributeInstance>, ClassConstraint),
}

#[derive(Clone, Debug, Node)]
pub struct ClassItemDeclaration {
    pub nodes: (Vec<AttributeInstance>, ClassDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct ClassItemCovergroup {
    pub nodes: (Vec<AttributeInstance>, CovergroupDeclaration),
}

#[derive(Clone, Debug, Node)]
pub enum ClassProperty {
    NonConst(ClassPropertyNonConst),
    Const(ClassPropertyConst),
}

#[derive(Clone, Debug, Node)]
pub struct ClassPropertyNonConst {
    pub nodes: (Vec<PropertyQualifier>, DataDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct ClassPropertyConst {
    pub nodes: (
        Keyword,
        Vec<ClassItemQualifier>,
        DataType,
        ConstIdentifier,
        Option<(Symbol, ConstantExpression)>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum ClassMethod {
    Task(ClassMethodTask),
    Function(ClassMethodFunction),
    PureVirtual(ClassMethodPureVirtual),
    ExternMethod(ClassMethodExternMethod),
    Constructor(ClassMethodConstructor),
    ExternConstructor(ClassMethodExternConstructor),
}

#[derive(Clone, Debug, Node)]
pub struct ClassMethodTask {
    pub nodes: (Vec<MethodQualifier>, TaskDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct ClassMethodFunction {
    pub nodes: (Vec<MethodQualifier>, FunctionDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct ClassMethodPureVirtual {
    pub nodes: (
        Keyword,
        Keyword,
        Vec<ClassItemQualifier>,
        MethodPrototype,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ClassMethodExternMethod {
    pub nodes: (Keyword, Vec<MethodQualifier>, MethodPrototype, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct ClassMethodConstructor {
    pub nodes: (Vec<MethodQualifier>, ClassConstructorDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct ClassMethodExternConstructor {
    pub nodes: (Keyword, Vec<MethodQualifier>, ClassConstructorPrototype),
}

#[derive(Clone, Debug, Node)]
pub struct ClassConstructorPrototype {
    pub nodes: (Keyword, Keyword, Option<Paren<Option<TfPortList>>>, Symbol),
}

#[derive(Clone, Debug, Node)]
pub enum ClassConstraint {
    ConstraintPrototype(ConstraintPrototype),
    ConstraintDeclaration(ConstraintDeclaration),
}

#[derive(Clone, Debug, Node)]
pub enum ClassItemQualifier {
    Static(Keyword),
    Protected(Keyword),
    Local(Keyword),
}

#[derive(Clone, Debug, Node)]
pub enum PropertyQualifier {
    RandomQualifier(RandomQualifier),
    ClassItemQualifier(ClassItemQualifier),
}

#[derive(Clone, Debug, Node)]
pub enum RandomQualifier {
    Rand(Keyword),
    Randc(Keyword),
}

#[derive(Clone, Debug, Node)]
pub enum MethodQualifier {
    Virtual(Keyword),
    PureVirtual((Keyword, Keyword)),
    ClassItemQualifier(ClassItemQualifier),
}

#[derive(Clone, Debug, Node)]
pub enum MethodPrototype {
    TaskPrototype(TaskPrototype),
    FunctionPrototype(FunctionPrototype),
}

#[derive(Clone, Debug, Node)]
pub struct ClassConstructorDeclaration {
    pub nodes: (
        Keyword,
        Option<ClassScope>,
        Keyword,
        Option<Paren<Option<TfPortList>>>,
        Symbol,
        Vec<BlockItemDeclaration>,
        Option<(
            Keyword,
            Symbol,
            Keyword,
            Option<Paren<ListOfArguments>>,
            Symbol,
        )>,
        Vec<FunctionStatementOrNull>,
        Keyword,
        Option<(Symbol, New)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct New {
    pub nodes: (Keyword,),
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
    let (s, a) = keyword("const")(s)?;
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
    let (s, a) = keyword("pure")(s)?;
    let (s, b) = keyword("virtual")(s)?;
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
    let (s, a) = keyword("extern")(s)?;
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
    let (s, a) = keyword("extern")(s)?;
    let (s, b) = many0(method_qualifier)(s)?;
    let (s, c) = class_constructor_prototype(s)?;
    Ok((
        s,
        ClassMethod::ExternConstructor(ClassMethodExternConstructor { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn class_constructor_prototype(s: Span) -> IResult<Span, ClassConstructorPrototype> {
    let (s, a) = keyword("function")(s)?;
    let (s, b) = keyword("new")(s)?;
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
        map(keyword("static"), |x| ClassItemQualifier::Static(x)),
        map(keyword("protected"), |x| ClassItemQualifier::Protected(x)),
        map(keyword("local"), |x| ClassItemQualifier::Local(x)),
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
        map(keyword("randc"), |x| RandomQualifier::Randc(x)),
        map(keyword("rand"), |x| RandomQualifier::Rand(x)),
    ))(s)
}

#[parser]
pub fn method_qualifier(s: Span) -> IResult<Span, MethodQualifier> {
    alt((
        map(pair(keyword("pure"), keyword("virtual")), |x| {
            MethodQualifier::PureVirtual(x)
        }),
        map(keyword("virtual"), |x| MethodQualifier::Virtual(x)),
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
    let (s, a) = keyword("function")(s)?;
    let (s, b) = opt(class_scope)(s)?;
    let (s, c) = keyword("new")(s)?;
    let (s, d) = opt(paren(opt(tf_port_list)))(s)?;
    let (s, e) = symbol(";")(s)?;
    let (s, f) = many0(block_item_declaration)(s)?;
    let (s, g) = opt(tuple((
        keyword("super"),
        symbol("."),
        keyword("new"),
        opt(paren(list_of_arguments)),
        symbol(";"),
    )))(s)?;
    let (s, h) = many0(function_statement_or_null)(s)?;
    let (s, i) = keyword("end")(s)?;
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
    let (s, a) = keyword("new")(s)?;
    Ok((s, New { nodes: (a,) }))
}
