use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct Concatenation {
    pub nodes: (Brace<List<Symbol, Expression>>,),
}

#[derive(Clone, Debug, Node)]
pub struct ConstantConcatenation {
    pub nodes: (Brace<List<Symbol, ConstantExpression>>,),
}

#[derive(Clone, Debug, Node)]
pub struct ConstantMultipleConcatenation {
    pub nodes: (Brace<(ConstantExpression, ConstantConcatenation)>,),
}

#[derive(Clone, Debug, Node)]
pub struct ModulePathConcatenation {
    pub nodes: (Brace<List<Symbol, ModulePathExpression>>,),
}

#[derive(Clone, Debug, Node)]
pub struct ModulePathMultipleConcatenation {
    pub nodes: (Brace<(ConstantExpression, ModulePathConcatenation)>,),
}

#[derive(Clone, Debug, Node)]
pub struct MultipleConcatenation {
    pub nodes: (Brace<(Expression, Concatenation)>,),
}

#[derive(Clone, Debug, Node)]
pub struct StreamingConcatenation {
    pub nodes: (Brace<(StreamOperator, Option<SliceSize>, StreamConcatenation)>,),
}

#[derive(Clone, Debug, Node)]
pub struct StreamOperator {
    pub nodes: (Symbol,),
}

#[derive(Clone, Debug, Node)]
pub enum SliceSize {
    SimpleType(Box<SimpleType>),
    ConstantExpression(Box<ConstantExpression>),
}

#[derive(Clone, Debug, Node)]
pub struct StreamConcatenation {
    pub nodes: (Brace<List<Symbol, StreamExpression>>,),
}

#[derive(Clone, Debug, Node)]
pub struct StreamExpression {
    pub nodes: (Expression, Option<(Keyword, Bracket<ArrayRangeExpression>)>),
}

#[derive(Clone, Debug, Node)]
pub enum ArrayRangeExpression {
    Expression(Box<Expression>),
    Colon(Box<ArrayRangeExpressionColon>),
    PlusColon(Box<ArrayRangeExpressionPlusColon>),
    MinusColon(Box<ArrayRangeExpressionMinusColon>),
}

#[derive(Clone, Debug, Node)]
pub struct ArrayRangeExpressionColon {
    pub nodes: (Expression, Symbol, Expression),
}

#[derive(Clone, Debug, Node)]
pub struct ArrayRangeExpressionPlusColon {
    pub nodes: (Expression, Symbol, Expression),
}

#[derive(Clone, Debug, Node)]
pub struct ArrayRangeExpressionMinusColon {
    pub nodes: (Expression, Symbol, Expression),
}

#[derive(Clone, Debug, Node)]
pub struct EmptyUnpackedArrayConcatenation {
    pub nodes: (Symbol, Symbol),
}
