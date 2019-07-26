use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct ArrayIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct BlockIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct BinIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct CIdentifier {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

#[derive(Clone, Debug, Node)]
pub struct CellIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct CheckerIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct ClassIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct ClassVariableIdentifier {
    pub nodes: (VariableIdentifier,),
}

#[derive(Clone, Debug, Node)]
pub struct ClockingIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct ConfigIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct ConstIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct ConstraintIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct CovergroupIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct CovergroupVariableIdentifier {
    pub nodes: (VariableIdentifier,),
}

#[derive(Clone, Debug, Node)]
pub struct CoverPointIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct CrossIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct DynamicArrayVariableIdentifier {
    pub nodes: (VariableIdentifier,),
}

#[derive(Clone, Debug, Node)]
pub struct EnumIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct EscapedIdentifier {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

#[derive(Clone, Debug, Node)]
pub struct FormalIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct FormalPortIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct FunctionIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct GenerateBlockIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct GenvarIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct HierarchicalArrayIdentifier {
    pub nodes: (HierarchicalIdentifier,),
}

#[derive(Clone, Debug, Node)]
pub struct HierarchicalBlockIdentifier {
    pub nodes: (HierarchicalIdentifier,),
}

#[derive(Clone, Debug, Node)]
pub struct HierarchicalEventIdentifier {
    pub nodes: (HierarchicalIdentifier,),
}

#[derive(Clone, Debug, Node)]
pub struct HierarchicalIdentifier {
    pub nodes: (
        Option<Root>,
        Vec<(Identifier, ConstantBitSelect, Symbol)>,
        Identifier,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct Root {
    pub nodes: (Keyword, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct HierarchicalNetIdentifier {
    pub nodes: (HierarchicalIdentifier,),
}

#[derive(Clone, Debug, Node)]
pub struct HierarchicalParameterIdentifier {
    pub nodes: (HierarchicalIdentifier,),
}

#[derive(Clone, Debug, Node)]
pub struct HierarchicalPropertyIdentifier {
    pub nodes: (HierarchicalIdentifier,),
}

#[derive(Clone, Debug, Node)]
pub struct HierarchicalSequenceIdentifier {
    pub nodes: (HierarchicalIdentifier,),
}

#[derive(Clone, Debug, Node)]
pub struct HierarchicalTaskIdentifier {
    pub nodes: (HierarchicalIdentifier,),
}

#[derive(Clone, Debug, Node)]
pub struct HierarchicalTfIdentifier {
    pub nodes: (HierarchicalIdentifier,),
}

#[derive(Clone, Debug, Node)]
pub struct HierarchicalVariableIdentifier {
    pub nodes: (HierarchicalIdentifier,),
}

#[derive(Clone, Debug, Node)]
pub enum Identifier {
    SimpleIdentifier(Box<SimpleIdentifier>),
    EscapedIdentifier(Box<EscapedIdentifier>),
}

#[derive(Clone, Debug, Node)]
pub struct IndexVariableIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct InterfaceIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct InterfaceInstanceIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct InoutPortIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct InputPortIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct InstanceIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct LibraryIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct MemberIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct MethodIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct ModportIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct ModuleIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct NetIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct NetTypeIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct OutputPortIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct PackageIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub enum PackageScope {
    Package(Box<PackageScopePackage>),
    Unit(Box<Unit>),
}

#[derive(Clone, Debug, Node)]
pub struct PackageScopePackage {
    pub nodes: (PackageIdentifier, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct Unit {
    pub nodes: (Keyword, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct ParameterIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct PortIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct ProductionIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct ProgramIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct PsClassIdentifier {
    pub nodes: (Option<PackageScope>, ClassIdentifier),
}

#[derive(Clone, Debug, Node)]
pub struct PsCovergroupIdentifier {
    pub nodes: (Option<PackageScope>, CovergroupIdentifier),
}

#[derive(Clone, Debug, Node)]
pub struct PsCheckerIdentifier {
    pub nodes: (Option<PackageScope>, CheckerIdentifier),
}

#[derive(Clone, Debug, Node)]
pub struct PsIdentifier {
    pub nodes: (Option<PackageScope>, Identifier),
}

#[derive(Clone, Debug, Node)]
pub struct PsOrHierarchicalArrayIdentifier {
    pub nodes: (
        Option<ImplicitClassHandleOrClassScopeOrPackageScope>,
        HierarchicalArrayIdentifier,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum PsOrHierarchicalNetIdentifier {
    PackageScope(Box<PsOrHierarchicalNetIdentifierPackageScope>),
    HierarchicalNetIdentifier(Box<HierarchicalNetIdentifier>),
}

#[derive(Clone, Debug, Node)]
pub struct PsOrHierarchicalNetIdentifierPackageScope {
    pub nodes: (Option<PackageScope>, NetIdentifier),
}

#[derive(Clone, Debug, Node)]
pub struct PsOrHierarchicalNetIdentifierHierarchical {
    pub nodes: (HierarchicalNetIdentifier),
}

#[derive(Clone, Debug, Node)]
pub enum PsOrHierarchicalPropertyIdentifier {
    PackageScope(Box<PsOrHierarchicalPropertyIdentifierPackageScope>),
    HierarchicalPropertyIdentifier(Box<HierarchicalPropertyIdentifier>),
}

#[derive(Clone, Debug, Node)]
pub struct PsOrHierarchicalPropertyIdentifierPackageScope {
    pub nodes: (Option<PackageScope>, PropertyIdentifier),
}

#[derive(Clone, Debug, Node)]
pub struct PsOrHierarchicalPropertyIdentifierHierarchical {
    pub nodes: (HierarchicalPropertyIdentifier),
}

#[derive(Clone, Debug, Node)]
pub enum PsOrHierarchicalSequenceIdentifier {
    PackageScope(Box<PsOrHierarchicalSequenceIdentifierPackageScope>),
    HierarchicalSequenceIdentifier(Box<HierarchicalSequenceIdentifier>),
}

#[derive(Clone, Debug, Node)]
pub struct PsOrHierarchicalSequenceIdentifierPackageScope {
    pub nodes: (Option<PackageScope>, SequenceIdentifier),
}

#[derive(Clone, Debug, Node)]
pub struct PsOrHierarchicalSequenceIdentifierHierarchical {
    pub nodes: (HierarchicalSequenceIdentifier),
}

#[derive(Clone, Debug, Node)]
pub enum PsOrHierarchicalTfIdentifier {
    PackageScope(Box<PsOrHierarchicalTfIdentifierPackageScope>),
    HierarchicalTfIdentifier(Box<HierarchicalTfIdentifier>),
}

#[derive(Clone, Debug, Node)]
pub struct PsOrHierarchicalTfIdentifierPackageScope {
    pub nodes: (Option<PackageScope>, TfIdentifier),
}

#[derive(Clone, Debug, Node)]
pub struct PsOrHierarchicalTfIdentifierHierarchical {
    pub nodes: (HierarchicalTfIdentifier),
}

#[derive(Clone, Debug, Node)]
pub enum PsParameterIdentifier {
    Scope(Box<PsParameterIdentifierScope>),
    Generate(Box<PsParameterIdentifierGenerate>),
}

#[derive(Clone, Debug, Node)]
pub struct PsParameterIdentifierScope {
    pub nodes: (Option<PackageScopeOrClassScope>, ParameterIdentifier),
}

#[derive(Clone, Debug, Node)]
pub struct PsParameterIdentifierGenerate {
    pub nodes: (
        Vec<(
            GenerateBlockIdentifier,
            Option<Bracket<ConstantExpression>>,
            Symbol,
        )>,
        ParameterIdentifier,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct PsTypeIdentifier {
    pub nodes: (Option<LocalOrPackageScopeOrClassScope>, TypeIdentifier),
}

#[derive(Clone, Debug, Node)]
pub enum LocalOrPackageScopeOrClassScope {
    Local(Box<Local>),
    PackageScope(Box<PackageScope>),
    ClassScope(Box<ClassScope>),
}

#[derive(Clone, Debug, Node)]
pub struct Local {
    pub nodes: (Keyword, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct SequenceIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct SignalIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct SimpleIdentifier {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

#[derive(Clone, Debug, Node)]
pub struct SpecparamIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct SystemTfIdentifier {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

#[derive(Clone, Debug, Node)]
pub struct TaskIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct TfIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct TerminalIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct TopmoduleIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct TypeIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct UdpIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct VariableIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub enum ImplicitClassHandleOrClassScopeOrPackageScope {
    ImplicitClassHandle(Box<(ImplicitClassHandle, Symbol)>),
    ClassScope(Box<ClassScope>),
    PackageScope(Box<PackageScope>),
}

#[derive(Clone, Debug, Node)]
pub enum ImplicitClassHandleOrPackageScope {
    ImplicitClassHandle(Box<(ImplicitClassHandle, Symbol)>),
    PackageScope(Box<PackageScope>),
}

#[derive(Clone, Debug, Node)]
pub enum ImplicitClassHandleOrClassScope {
    ImplicitClassHandle(Box<(ImplicitClassHandle, Symbol)>),
    ClassScope(Box<ClassScope>),
}

#[derive(Clone, Debug, Node)]
pub enum PackageScopeOrClassScope {
    PackageScope(Box<PackageScope>),
    ClassScope(Box<ClassScope>),
}
