use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum ClassItem<'a> {
    Property(ClassItemProperty<'a>),
    Method(ClassItemMethod<'a>),
    Constraint(ClassItemConstraint<'a>),
    Declaration(ClassItemDeclaration<'a>),
    Covergroup(ClassItemCovergroup<'a>),
    LocalParameterDeclaration(LocalParameterDeclaration<'a>),
    ParameterDeclaration(ParameterDeclaration<'a>),
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
        Vec<ClassItemQualifier<'a>>,
        DataType<'a>,
        ConstIdentifier<'a>,
        Option<ConstantExpression<'a>>,
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
    pub nodes: (Vec<ClassItemQualifier<'a>>, MethodPrototype<'a>),
}

#[derive(Debug, Node)]
pub struct ClassMethodExternMethod<'a> {
    pub nodes: (Vec<MethodQualifier<'a>>, MethodPrototype<'a>),
}

#[derive(Debug, Node)]
pub struct ClassMethodConstructor<'a> {
    pub nodes: (Vec<MethodQualifier<'a>>, ClassConstructorPrototype<'a>),
}

#[derive(Debug, Node)]
pub struct ClassMethodExternConstructor<'a> {
    pub nodes: (Vec<MethodQualifier<'a>>, ClassConstructorPrototype<'a>),
}

#[derive(Debug, Node)]
pub struct ClassConstructorPrototype<'a> {
    pub nodes: (Option<TfPortList<'a>>,),
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
    PureVirtual(Symbol<'a>),
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
        Option<ClassScope<'a>>,
        Option<Option<TfPortList<'a>>>,
        Vec<BlockItemDeclaration<'a>>,
        Option<Option<ListOfArguments<'a>>>,
        Vec<FunctionStatementOrNull<'a>>,
        Option<New<'a>>,
    ),
}

#[derive(Debug, Node)]
pub struct New<'a> {
    pub nodes: (Symbol<'a>,),
}

// -----------------------------------------------------------------------------

pub fn class_item(s: Span) -> IResult<Span, ClassItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn class_property(s: Span) -> IResult<Span, ClassProperty> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn class_method(s: Span) -> IResult<Span, ClassMethod> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn class_constructor_prototype(s: Span) -> IResult<Span, ClassConstructorPrototype> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn class_constraint(s: Span) -> IResult<Span, ClassConstraint> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn class_item_qualifier(s: Span) -> IResult<Span, ClassItemQualifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_qualifier(s: Span) -> IResult<Span, PropertyQualifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn random_qualifier(s: Span) -> IResult<Span, RandomQualifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn method_qualifier(s: Span) -> IResult<Span, MethodQualifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn method_prototype(s: Span) -> IResult<Span, MethodPrototype> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn class_constructor_declaration(s: Span) -> IResult<Span, ClassConstructorDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}
