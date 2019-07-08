use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum ClassItem<'a> {
    Property(ClassItemProperty<'a>),
    Method(ClassItemMethod<'a>),
    Constraint(ClassItemConstraint<'a>),
    Declaration(ClassItemDeclaration<'a>),
    Covergroup(ClassItemCovergroup<'a>),
    LocalParameterDeclaration(LocalParameterDeclaration<'a>),
    ParameterDeclaration(ParameterDeclaration<'a>),
    Empty,
}

#[derive(Debug)]
pub struct ClassItemProperty<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ClassProperty<'a>),
}

#[derive(Debug)]
pub struct ClassItemMethod<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ClassMethod<'a>),
}

#[derive(Debug)]
pub struct ClassItemConstraint<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ClassConstraint<'a>),
}

#[derive(Debug)]
pub struct ClassItemDeclaration<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ClassDeclaration<'a>),
}

#[derive(Debug)]
pub struct ClassItemCovergroup<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, CovergroupDeclaration<'a>),
}

#[derive(Debug)]
pub enum ClassProperty<'a> {
    NonConst(ClassPropertyNonConst<'a>),
    Const(ClassPropertyConst<'a>),
}

#[derive(Debug)]
pub struct ClassPropertyNonConst<'a> {
    pub nodes: (Vec<PropertyQualifier>, DataDeclaration<'a>),
}

#[derive(Debug)]
pub struct ClassPropertyConst<'a> {
    pub nodes: (
        Vec<ClassItemQualifier>,
        DataType<'a>,
        ConstIdentifier<'a>,
        Option<ConstantExpression<'a>>,
    ),
}

#[derive(Debug)]
pub enum ClassMethod<'a> {
    Task(ClassMethodTask<'a>),
    Function(ClassMethodFunction<'a>),
    PureVirtual(ClassMethodPureVirtual<'a>),
    ExternMethod(ClassMethodExternMethod<'a>),
    Constructor(ClassMethodConstructor<'a>),
    ExternConstructor(ClassMethodExternConstructor<'a>),
}

#[derive(Debug)]
pub struct ClassMethodTask<'a> {
    pub nodes: (Vec<MethodQualifier>, TaskDeclaration<'a>),
}

#[derive(Debug)]
pub struct ClassMethodFunction<'a> {
    pub nodes: (Vec<MethodQualifier>, FunctionDeclaration<'a>),
}

#[derive(Debug)]
pub struct ClassMethodPureVirtual<'a> {
    pub nodes: (Vec<ClassItemQualifier>, MethodPrototype<'a>),
}

#[derive(Debug)]
pub struct ClassMethodExternMethod<'a> {
    pub nodes: (Vec<MethodQualifier>, MethodPrototype<'a>),
}

#[derive(Debug)]
pub struct ClassMethodConstructor<'a> {
    pub nodes: (Vec<MethodQualifier>, ClassConstructorPrototype<'a>),
}

#[derive(Debug)]
pub struct ClassMethodExternConstructor<'a> {
    pub nodes: (Vec<MethodQualifier>, ClassConstructorPrototype<'a>),
}

#[derive(Debug)]
pub struct ClassConstructorPrototype<'a> {
    pub nodes: (Option<TfPortList<'a>>,),
}

#[derive(Debug)]
pub enum ClassConstraint<'a> {
    ConstraintPrototype(ConstraintPrototype<'a>),
    ConstraintDeclaration(ConstraintDeclaration<'a>),
}

#[derive(Debug)]
pub enum ClassItemQualifier {
    Static,
    Protected,
    Local,
}

#[derive(Debug)]
pub enum PropertyQualifier {
    RandomQualifier(RandomQualifier),
    ClassItemQualifier(ClassItemQualifier),
}

#[derive(Debug)]
pub enum RandomQualifier {
    Rand,
    Randc,
}

#[derive(Debug)]
pub enum MethodQualifier {
    Virtual,
    PureVirtual,
    ClassItemQualifier(ClassItemQualifier),
}

#[derive(Debug)]
pub enum MethodPrototype<'a> {
    TaskPrototype(TaskPrototype<'a>),
    FunctionPrototype(FunctionPrototype<'a>),
}

#[derive(Debug)]
pub struct ClassConstructorDeclaration<'a> {
    pub nodes: (
        Option<ClassScope<'a>>,
        Option<Option<TfPortList<'a>>>,
        Vec<BlockItemDeclaration<'a>>,
        Option<Option<ListOfArguments<'a>>>,
        Vec<FunctionStatementOrNull<'a>>,
        Option<New>,
    ),
}

#[derive(Debug)]
pub struct New {}

// -----------------------------------------------------------------------------

pub fn class_item(s: &str) -> IResult<&str, ClassItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn class_property(s: &str) -> IResult<&str, ClassProperty> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn class_method(s: &str) -> IResult<&str, ClassMethod> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn class_constructor_prototype(s: &str) -> IResult<&str, ClassConstructorPrototype> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn class_constraint(s: &str) -> IResult<&str, ClassConstraint> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn class_item_qualifier(s: &str) -> IResult<&str, ClassItemQualifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_qualifier(s: &str) -> IResult<&str, PropertyQualifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn random_qualifier(s: &str) -> IResult<&str, RandomQualifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn method_qualifier(s: &str) -> IResult<&str, MethodQualifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn class_constructor_declaration(s: &str) -> IResult<&str, ClassConstructorDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}
