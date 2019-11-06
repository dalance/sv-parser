use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub enum CompilerDirective {
    ResetallCompilerDirective(Box<ResetallCompilerDirective>),
    IncludeCompilerDirective(Box<IncludeCompilerDirective>),
    TextMacroDefinition(Box<TextMacroDefinition>),
    TextMacroUsage(Box<TextMacroUsage>),
    UndefineCompilerDirective(Box<UndefineCompilerDirective>),
    UndefineallCompilerDirective(Box<UndefineallCompilerDirective>),
    ConditionalCompilerDirective(Box<ConditionalCompilerDirective>),
    TimescaleCompilerDirective(Box<TimescaleCompilerDirective>),
    DefaultNettypeCompilerDirective(Box<DefaultNettypeCompilerDirective>),
    UnconnectedDriveCompilerDirective(Box<UnconnectedDriveCompilerDirective>),
    NounconnectedDriveCompilerDirective(Box<NounconnectedDriveCompilerDirective>),
    CelldefineDriveCompilerDirective(Box<CelldefineDriveCompilerDirective>),
    EndcelldefineDriveCompilerDirective(Box<EndcelldefineDriveCompilerDirective>),
    Pragma(Box<Pragma>),
    LineCompilerDirective(Box<LineCompilerDirective>),
    PositionCompilerDirective(Box<PositionCompilerDirective>),
    KeywordsDirective(Box<KeywordsDirective>),
    EndkeywordsDirective(Box<EndkeywordsDirective>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ResetallCompilerDirective {
    pub nodes: (Symbol, Keyword),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum IncludeCompilerDirective {
    DoubleQuote(Box<IncludeCompilerDirectiveDoubleQuote>),
    AngleBracket(Box<IncludeCompilerDirectiveAngleBracket>),
    TextMacroUsage(Box<IncludeCompilerDirectiveTextMacroUsage>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct IncludeCompilerDirectiveDoubleQuote {
    pub nodes: (Symbol, Keyword, StringLiteral),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct IncludeCompilerDirectiveAngleBracket {
    pub nodes: (Symbol, Keyword, AngleBracketLiteral),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct IncludeCompilerDirectiveTextMacroUsage {
    pub nodes: (Symbol, Keyword, TextMacroUsage),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct AngleBracketLiteral {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TextMacroDefinition {
    pub nodes: (Symbol, Keyword, TextMacroName, Option<MacroText>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TextMacroName {
    pub nodes: (TextMacroIdentifier, Option<Paren<ListOfFormalArguments>>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ListOfFormalArguments {
    pub nodes: (List<Symbol, FormalArgument>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct FormalArgument {
    pub nodes: (SimpleIdentifier, Option<(Symbol, DefaultText)>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TextMacroIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct MacroText {
    pub nodes: (Locate,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct DefaultText {
    pub nodes: (Locate,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TextMacroUsage {
    pub nodes: (
        Symbol,
        TextMacroIdentifier,
        Option<Paren<ListOfActualArguments>>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ListOfActualArguments {
    pub nodes: (List<Symbol, Option<ActualArgument>>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ActualArgument {
    pub nodes: (Locate,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct UndefineCompilerDirective {
    pub nodes: (Symbol, Keyword, TextMacroIdentifier),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct UndefineallCompilerDirective {
    pub nodes: (Symbol, Keyword),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ConditionalCompilerDirective {
    IfdefDirective(Box<IfdefDirective>),
    IfndefDirective(Box<IfndefDirective>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct IfdefDirective {
    pub nodes: (
        Symbol,
        Keyword,
        TextMacroIdentifier,
        IfdefGroupOfLines,
        Vec<(Symbol, Keyword, TextMacroIdentifier, ElsifGroupOfLines)>,
        Option<(Symbol, Keyword, ElseGroupOfLines)>,
        Symbol,
        Keyword,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct IfndefDirective {
    pub nodes: (
        Symbol,
        Keyword,
        TextMacroIdentifier,
        IfndefGroupOfLines,
        Vec<(Symbol, Keyword, TextMacroIdentifier, ElsifGroupOfLines)>,
        Option<(Symbol, Keyword, ElseGroupOfLines)>,
        Symbol,
        Keyword,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct IfdefGroupOfLines {
    pub nodes: (Vec<SourceDescription>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct IfndefGroupOfLines {
    pub nodes: (Vec<SourceDescription>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ElsifGroupOfLines {
    pub nodes: (Vec<SourceDescription>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ElseGroupOfLines {
    pub nodes: (Vec<SourceDescription>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum SourceDescription {
    Comment(Box<Comment>),
    StringLiteral(Box<StringLiteral>),
    NotDirective(Box<SourceDescriptionNotDirective>),
    CompilerDirective(Box<CompilerDirective>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SourceDescriptionNotDirective {
    pub nodes: (Locate,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TimescaleCompilerDirective {
    pub nodes: (Symbol, Keyword, TimeLiteral, Symbol, TimeLiteral),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct DefaultNettypeCompilerDirective {
    pub nodes: (Symbol, Keyword, DefaultNettypeValue),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct DefaultNettypeValue {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct UnconnectedDriveCompilerDirective {
    pub nodes: (Symbol, Keyword, Keyword),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct NounconnectedDriveCompilerDirective {
    pub nodes: (Symbol, Keyword),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CelldefineDriveCompilerDirective {
    pub nodes: (Symbol, Keyword),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct EndcelldefineDriveCompilerDirective {
    pub nodes: (Symbol, Keyword),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct Pragma {
    pub nodes: (
        Symbol,
        Keyword,
        PragmaName,
        Option<List<Symbol, PragmaExpression>>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PragmaName {
    pub nodes: (SimpleIdentifier,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum PragmaExpression {
    PragmaKeyword(Box<PragmaKeyword>),
    Assignment(Box<PragmaExpressionAssignment>),
    PragmaValue(Box<PragmaValue>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PragmaExpressionAssignment {
    pub nodes: (PragmaKeyword, Symbol, PragmaValue),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum PragmaValue {
    Paren(Box<PragmaValueParen>),
    Number(Box<Number>),
    StringLiteral(Box<StringLiteral>),
    Identifier(Box<Identifier>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PragmaValueParen {
    pub nodes: (Paren<List<Symbol, PragmaExpression>>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PragmaKeyword {
    pub nodes: (SimpleIdentifier,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct LineCompilerDirective {
    pub nodes: (Symbol, Keyword, Number, StringLiteral, Level),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PositionCompilerDirective {
    pub nodes: (Symbol, Keyword),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct Level {
    pub nodes: (Symbol,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct KeywordsDirective {
    pub nodes: (Symbol, Keyword, Symbol, VersionSpecifier, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct VersionSpecifier {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct EndkeywordsDirective {
    pub nodes: (Symbol, Keyword),
}
