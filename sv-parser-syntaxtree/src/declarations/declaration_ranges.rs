use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub enum UnpackedDimension {
    Range(Box<UnpackedDimensionRange>),
    Expression(Box<UnpackedDimensionExpression>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct UnpackedDimensionRange {
    pub nodes: (Bracket<ConstantRange>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct UnpackedDimensionExpression {
    pub nodes: (Bracket<ConstantExpression>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum PackedDimension {
    Range(Box<PackedDimensionRange>),
    UnsizedDimension(Box<UnsizedDimension>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PackedDimensionRange {
    pub nodes: (Bracket<ConstantRange>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum AssociativeDimension {
    DataType(Box<AssociativeDimensionDataType>),
    Asterisk(Box<AssociativeDimensionAsterisk>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct AssociativeDimensionDataType {
    pub nodes: (Bracket<DataType>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct AssociativeDimensionAsterisk {
    pub nodes: (Bracket<Symbol>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum VariableDimension {
    UnsizedDimension(Box<UnsizedDimension>),
    UnpackedDimension(Box<UnpackedDimension>),
    AssociativeDimension(Box<AssociativeDimension>),
    QueueDimension(Box<QueueDimension>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct QueueDimension {
    pub nodes: (Bracket<(Symbol, Option<(Symbol, ConstantExpression)>)>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct UnsizedDimension {
    pub nodes: (Symbol, Symbol),
}
