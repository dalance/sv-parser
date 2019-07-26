use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum StatementOrNull {
    Statement(Box<Statement>),
    Attribute(Box<StatementOrNullAttribute>),
}

#[derive(Clone, Debug, Node)]
pub struct StatementOrNullAttribute {
    pub nodes: (Vec<AttributeInstance>, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct Statement {
    pub nodes: (
        Option<(BlockIdentifier, Symbol)>,
        Vec<AttributeInstance>,
        StatementItem,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum StatementItem {
    BlockingAssignment(Box<(BlockingAssignment, Symbol)>),
    NonblockingAssignment(Box<(NonblockingAssignment, Symbol)>),
    ProceduralContinuousAssignment(Box<(ProceduralContinuousAssignment, Symbol)>),
    CaseStatement(Box<CaseStatement>),
    ConditionalStatement(Box<ConditionalStatement>),
    IncOrDecExpression(Box<(IncOrDecExpression, Symbol)>),
    SubroutineCallStatement(Box<SubroutineCallStatement>),
    DisableStatement(Box<DisableStatement>),
    EventTrigger(Box<EventTrigger>),
    LoopStatement(Box<LoopStatement>),
    JumpStatement(Box<JumpStatement>),
    ParBlock(Box<ParBlock>),
    ProceduralTimingControlStatement(Box<ProceduralTimingControlStatement>),
    SeqBlock(Box<SeqBlock>),
    WaitStatement(Box<WaitStatement>),
    ProceduralAssertionStatement(Box<ProceduralAssertionStatement>),
    ClockingDrive(Box<(ClockingDrive, Symbol)>),
    RandsequenceStatement(Box<RandsequenceStatement>),
    RandcaseStatement(Box<RandcaseStatement>),
    ExpectPropertyStatement(Box<ExpectPropertyStatement>),
}

#[derive(Clone, Debug, Node)]
pub struct FunctionStatement {
    pub nodes: (Statement,),
}

#[derive(Clone, Debug, Node)]
pub enum FunctionStatementOrNull {
    Statement(Box<FunctionStatement>),
    Attribute(Box<FunctionStatementOrNullAttribute>),
}

#[derive(Clone, Debug, Node)]
pub struct FunctionStatementOrNullAttribute {
    pub nodes: (Vec<AttributeInstance>, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct VariableIdentifierList {
    pub nodes: (List<Symbol, VariableIdentifier>,),
}
