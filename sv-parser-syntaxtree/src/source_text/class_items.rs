use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ClassItem {
    Property(Box<ClassItemProperty>),
    Method(Box<ClassItemMethod>),
    Constraint(Box<ClassItemConstraint>),
    Declaration(Box<ClassItemDeclaration>),
    Covergroup(Box<ClassItemCovergroup>),
    LocalParameterDeclaration(Box<(LocalParameterDeclaration, Symbol)>),
    ParameterDeclaration(Box<(ParameterDeclaration, Symbol)>),
    Empty(Box<Symbol>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ClassItemProperty {
    pub nodes: (Vec<AttributeInstance>, ClassProperty),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ClassItemMethod {
    pub nodes: (Vec<AttributeInstance>, ClassMethod),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ClassItemConstraint {
    pub nodes: (Vec<AttributeInstance>, ClassConstraint),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ClassItemDeclaration {
    pub nodes: (Vec<AttributeInstance>, ClassDeclaration),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ClassItemCovergroup {
    pub nodes: (Vec<AttributeInstance>, CovergroupDeclaration),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ClassProperty {
    NonConst(Box<ClassPropertyNonConst>),
    Const(Box<ClassPropertyConst>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ClassPropertyNonConst {
    pub nodes: (Vec<PropertyQualifier>, DataDeclaration),
}

#[derive(Clone, Debug, PartialEq, Node)]
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

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ClassMethod {
    Task(Box<ClassMethodTask>),
    Function(Box<ClassMethodFunction>),
    PureVirtual(Box<ClassMethodPureVirtual>),
    ExternMethod(Box<ClassMethodExternMethod>),
    Constructor(Box<ClassMethodConstructor>),
    ExternConstructor(Box<ClassMethodExternConstructor>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ClassMethodTask {
    pub nodes: (Vec<MethodQualifier>, TaskDeclaration),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ClassMethodFunction {
    pub nodes: (Vec<MethodQualifier>, FunctionDeclaration),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ClassMethodPureVirtual {
    pub nodes: (
        Keyword,
        Keyword,
        Vec<ClassItemQualifier>,
        MethodPrototype,
        Symbol,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ClassMethodExternMethod {
    pub nodes: (Keyword, Vec<MethodQualifier>, MethodPrototype, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ClassMethodConstructor {
    pub nodes: (Vec<MethodQualifier>, ClassConstructorDeclaration),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ClassMethodExternConstructor {
    pub nodes: (Keyword, Vec<MethodQualifier>, ClassConstructorPrototype),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ClassConstructorPrototype {
    pub nodes: (Keyword, Keyword, Option<Paren<Option<TfPortList>>>, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ClassConstraint {
    ConstraintPrototype(Box<ConstraintPrototype>),
    ConstraintDeclaration(Box<ConstraintDeclaration>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ClassItemQualifier {
    Static(Box<Keyword>),
    Protected(Box<Keyword>),
    Local(Box<Keyword>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum PropertyQualifier {
    RandomQualifier(Box<RandomQualifier>),
    ClassItemQualifier(Box<ClassItemQualifier>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum RandomQualifier {
    Rand(Box<Keyword>),
    Randc(Box<Keyword>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum MethodQualifier {
    Virtual(Box<Keyword>),
    PureVirtual(Box<(Keyword, Keyword)>),
    ClassItemQualifier(Box<ClassItemQualifier>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum MethodPrototype {
    TaskPrototype(Box<TaskPrototype>),
    FunctionPrototype(Box<FunctionPrototype>),
}

#[derive(Clone, Debug, PartialEq, Node)]
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

#[derive(Clone, Debug, PartialEq, Node)]
pub struct New {
    pub nodes: (Keyword,),
}
