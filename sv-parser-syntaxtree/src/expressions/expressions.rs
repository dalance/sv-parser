use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub enum IncOrDecExpression {
    Prefix(Box<IncOrDecExpressionPrefix>),
    Suffix(Box<IncOrDecExpressionSuffix>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct IncOrDecExpressionPrefix {
    pub nodes: (IncOrDecOperator, Vec<AttributeInstance>, VariableLvalue),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct IncOrDecExpressionSuffix {
    pub nodes: (VariableLvalue, Vec<AttributeInstance>, IncOrDecOperator),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ConditionalExpression {
    pub nodes: (
        CondPredicate,
        Symbol,
        Vec<AttributeInstance>,
        Expression,
        Symbol,
        Expression,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ConstantExpression {
    ConstantPrimary(Box<ConstantPrimary>),
    Unary(Box<ConstantExpressionUnary>),
    Binary(Box<ConstantExpressionBinary>),
    Ternary(Box<ConstantExpressionTernary>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ConstantExpressionUnary {
    pub nodes: (UnaryOperator, Vec<AttributeInstance>, ConstantPrimary),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ConstantExpressionBinary {
    pub nodes: (
        ConstantExpression,
        BinaryOperator,
        Vec<AttributeInstance>,
        ConstantExpression,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ConstantExpressionTernary {
    pub nodes: (
        ConstantExpression,
        Symbol,
        Vec<AttributeInstance>,
        ConstantExpression,
        Symbol,
        ConstantExpression,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ConstantMintypmaxExpression {
    Unary(Box<ConstantExpression>),
    Ternary(Box<ConstantMintypmaxExpressionTernary>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ConstantMintypmaxExpressionTernary {
    pub nodes: (
        ConstantExpression,
        Symbol,
        ConstantExpression,
        Symbol,
        ConstantExpression,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ConstantParamExpression {
    ConstantMintypmaxExpression(Box<ConstantMintypmaxExpression>),
    DataType(Box<DataType>),
    Dollar(Box<Symbol>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ParamExpression {
    MintypmaxExpression(Box<MintypmaxExpression>),
    DataType(Box<DataType>),
    Dollar(Box<Symbol>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ConstantRangeExpression {
    ConstantExpression(Box<ConstantExpression>),
    ConstantPartSelectRange(Box<ConstantPartSelectRange>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ConstantPartSelectRange {
    ConstantRange(Box<ConstantRange>),
    ConstantIndexedRange(Box<ConstantIndexedRange>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ConstantRange {
    pub nodes: (ConstantExpression, Symbol, ConstantExpression),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ConstantIndexedRange {
    pub nodes: (ConstantExpression, Symbol, ConstantExpression),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum Expression {
    Primary(Box<Primary>),
    Unary(Box<ExpressionUnary>),
    IncOrDecExpression(Box<IncOrDecExpression>),
    OperatorAssignment(Box<ExpressionOperatorAssignment>),
    Binary(Box<ExpressionBinary>),
    ConditionalExpression(Box<ConditionalExpression>),
    InsideExpression(Box<InsideExpression>),
    TaggedUnionExpression(Box<TaggedUnionExpression>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ExpressionUnary {
    pub nodes: (UnaryOperator, Vec<AttributeInstance>, Primary),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ExpressionOperatorAssignment {
    pub nodes: (Paren<OperatorAssignment>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ExpressionBinary {
    pub nodes: (
        Expression,
        BinaryOperator,
        Vec<AttributeInstance>,
        Expression,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TaggedUnionExpression {
    pub nodes: (Keyword, MemberIdentifier, Option<Expression>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct InsideExpression {
    pub nodes: (Expression, Keyword, Brace<OpenRangeList>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ValueRange {
    Expression(Box<Expression>),
    Binary(Box<ValueRangeBinary>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ValueRangeBinary {
    pub nodes: (Bracket<(Expression, Symbol, Expression)>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum MintypmaxExpression {
    Expression(Box<Expression>),
    Ternary(Box<MintypmaxExpressionTernary>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct MintypmaxExpressionTernary {
    pub nodes: (Expression, Symbol, Expression, Symbol, Expression),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ModulePathConditionalExpression {
    pub nodes: (
        ModulePathExpression,
        Symbol,
        Vec<AttributeInstance>,
        ModulePathExpression,
        Symbol,
        ModulePathExpression,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ModulePathExpression {
    ModulePathPrimary(Box<ModulePathPrimary>),
    Unary(Box<ModulePathExpressionUnary>),
    Binary(Box<ModulePathExpressionBinary>),
    ModulePathConditionalExpression(Box<ModulePathConditionalExpression>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ModulePathExpressionUnary {
    pub nodes: (
        UnaryModulePathOperator,
        Vec<AttributeInstance>,
        ModulePathPrimary,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ModulePathExpressionBinary {
    pub nodes: (
        ModulePathExpression,
        BinaryModulePathOperator,
        Vec<AttributeInstance>,
        ModulePathExpression,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ModulePathMintypmaxExpression {
    ModulePathExpression(Box<ModulePathExpression>),
    Ternary(Box<ModulePathMintypmaxExpressionTernary>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ModulePathMintypmaxExpressionTernary {
    pub nodes: (
        ModulePathExpression,
        Symbol,
        ModulePathExpression,
        Symbol,
        ModulePathExpression,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum PartSelectRange {
    ConstantRange(Box<ConstantRange>),
    IndexedRange(Box<IndexedRange>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct IndexedRange {
    pub nodes: (Expression, Symbol, ConstantExpression),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct GenvarExpression {
    pub nodes: (ConstantExpression,),
}
