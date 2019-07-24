use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::bytes::complete::*;
use nom::combinator::*;
use nom::error::*;
use nom::multi::*;
use nom::sequence::*;
use nom::{Err, IResult};
use nom_packrat::packrat_parser;

// -----------------------------------------------------------------------------

pub const AZ_: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_";
pub const AZ09_: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_";
pub const AZ09_DOLLAR: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_$";

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

// -----------------------------------------------------------------------------

#[parser]
pub fn array_identifier(s: Span) -> IResult<Span, ArrayIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ArrayIdentifier { nodes: (a,) }))
}

#[parser]
pub fn block_identifier(s: Span) -> IResult<Span, BlockIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, BlockIdentifier { nodes: (a,) }))
}

#[parser]
pub fn bin_identifier(s: Span) -> IResult<Span, BinIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, BinIdentifier { nodes: (a,) }))
}

#[parser]
pub fn c_identifier(s: Span) -> IResult<Span, CIdentifier> {
    let (s, a) = ws(c_identifier_impl)(s)?;
    Ok((s, CIdentifier { nodes: a }))
}

#[parser]
pub fn c_identifier_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = is_a(AZ_)(s)?;
    let (s, b) = opt(is_a(AZ09_))(s)?;
    let a = if let Some(b) = b {
        concat(a, b).unwrap()
    } else {
        a
    };
    if is_keyword(&a) {
        Err(Err::Error(make_error(s, ErrorKind::Fix)))
    } else {
        Ok((s, a.into()))
    }
}

#[parser]
pub fn cell_identifier(s: Span) -> IResult<Span, CellIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, CellIdentifier { nodes: (a,) }))
}

#[parser]
pub fn checker_identifier(s: Span) -> IResult<Span, CheckerIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, CheckerIdentifier { nodes: (a,) }))
}

#[parser]
pub fn class_identifier(s: Span) -> IResult<Span, ClassIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ClassIdentifier { nodes: (a,) }))
}

#[parser]
pub fn class_variable_identifier(s: Span) -> IResult<Span, ClassVariableIdentifier> {
    let (s, a) = variable_identifier(s)?;
    Ok((s, ClassVariableIdentifier { nodes: (a,) }))
}

#[parser]
pub fn clocking_identifier(s: Span) -> IResult<Span, ClockingIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ClockingIdentifier { nodes: (a,) }))
}

#[parser]
pub fn config_identifier(s: Span) -> IResult<Span, ConfigIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ConfigIdentifier { nodes: (a,) }))
}

#[parser]
pub fn const_identifier(s: Span) -> IResult<Span, ConstIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ConstIdentifier { nodes: (a,) }))
}

#[parser]
pub fn constraint_identifier(s: Span) -> IResult<Span, ConstraintIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ConstraintIdentifier { nodes: (a,) }))
}

#[parser]
pub fn covergroup_identifier(s: Span) -> IResult<Span, CovergroupIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, CovergroupIdentifier { nodes: (a,) }))
}

#[parser]
pub fn covergroup_variable_identifier(s: Span) -> IResult<Span, CovergroupVariableIdentifier> {
    let (s, a) = variable_identifier(s)?;
    Ok((s, CovergroupVariableIdentifier { nodes: (a,) }))
}

#[parser]
pub fn cover_point_identifier(s: Span) -> IResult<Span, CoverPointIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, CoverPointIdentifier { nodes: (a,) }))
}

#[parser]
pub fn cross_identifier(s: Span) -> IResult<Span, CrossIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, CrossIdentifier { nodes: (a,) }))
}

#[parser]
pub fn dynamic_array_variable_identifier(s: Span) -> IResult<Span, DynamicArrayVariableIdentifier> {
    let (s, a) = variable_identifier(s)?;
    Ok((s, DynamicArrayVariableIdentifier { nodes: (a,) }))
}

#[parser]
pub fn enum_identifier(s: Span) -> IResult<Span, EnumIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, EnumIdentifier { nodes: (a,) }))
}

#[parser]
pub fn escaped_identifier(s: Span) -> IResult<Span, EscapedIdentifier> {
    let (s, a) = ws(escaped_identifier_impl)(s)?;
    Ok((s, EscapedIdentifier { nodes: a }))
}

#[parser]
pub fn escaped_identifier_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = tag("\\")(s)?;
    let (s, b) = is_not(" \t\r\n")(s)?;
    let a = concat(a, b).unwrap();
    Ok((s, a.into()))
}

#[parser]
pub fn formal_identifier(s: Span) -> IResult<Span, FormalIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, FormalIdentifier { nodes: (a,) }))
}

#[parser]
pub fn formal_port_identifier(s: Span) -> IResult<Span, FormalPortIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, FormalPortIdentifier { nodes: (a,) }))
}

#[parser]
pub fn function_identifier(s: Span) -> IResult<Span, FunctionIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, FunctionIdentifier { nodes: (a,) }))
}

#[parser]
pub fn generate_block_identifier(s: Span) -> IResult<Span, GenerateBlockIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, GenerateBlockIdentifier { nodes: (a,) }))
}

#[parser]
pub fn genvar_identifier(s: Span) -> IResult<Span, GenvarIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, GenvarIdentifier { nodes: (a,) }))
}

#[parser]
pub fn hierarchical_array_identifier(s: Span) -> IResult<Span, HierarchicalArrayIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalArrayIdentifier { nodes: (a,) }))
}

#[parser]
pub fn hierarchical_block_identifier(s: Span) -> IResult<Span, HierarchicalBlockIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalBlockIdentifier { nodes: (a,) }))
}

#[parser]
pub fn hierarchical_event_identifier(s: Span) -> IResult<Span, HierarchicalEventIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalEventIdentifier { nodes: (a,) }))
}

#[packrat_parser]
#[parser]
pub fn hierarchical_identifier(s: Span) -> IResult<Span, HierarchicalIdentifier> {
    let (s, a) = opt(root)(s)?;
    let (s, b) = many0(triple(identifier, constant_bit_select, symbol(".")))(s)?;
    let (s, c) = identifier(s)?;
    Ok((s, HierarchicalIdentifier { nodes: (a, b, c) }))
}

#[parser]
pub fn root(s: Span) -> IResult<Span, Root> {
    let (s, a) = keyword("$root")(s)?;
    let (s, b) = symbol(".")(s)?;
    Ok((s, Root { nodes: (a, b) }))
}

#[parser]
pub fn hierarchical_net_identifier(s: Span) -> IResult<Span, HierarchicalNetIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalNetIdentifier { nodes: (a,) }))
}

#[parser]
pub fn hierarchical_parameter_identifier(
    s: Span,
) -> IResult<Span, HierarchicalParameterIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalParameterIdentifier { nodes: (a,) }))
}

#[parser]
pub fn hierarchical_property_identifier(s: Span) -> IResult<Span, HierarchicalPropertyIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalPropertyIdentifier { nodes: (a,) }))
}

#[parser]
pub fn hierarchical_sequence_identifier(s: Span) -> IResult<Span, HierarchicalSequenceIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalSequenceIdentifier { nodes: (a,) }))
}

#[parser]
pub fn hierarchical_task_identifier(s: Span) -> IResult<Span, HierarchicalTaskIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalTaskIdentifier { nodes: (a,) }))
}

#[parser]
pub fn hierarchical_tf_identifier(s: Span) -> IResult<Span, HierarchicalTfIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalTfIdentifier { nodes: (a,) }))
}

#[parser]
pub fn hierarchical_variable_identifier(s: Span) -> IResult<Span, HierarchicalVariableIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalVariableIdentifier { nodes: (a,) }))
}

#[packrat_parser]
#[parser]
pub fn identifier(s: Span) -> IResult<Span, Identifier> {
    alt((
        map(escaped_identifier, |x| {
            Identifier::EscapedIdentifier(Box::new(x))
        }),
        map(simple_identifier, |x| {
            Identifier::SimpleIdentifier(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn index_variable_identifier(s: Span) -> IResult<Span, IndexVariableIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, IndexVariableIdentifier { nodes: (a,) }))
}

#[parser]
pub fn interface_identifier(s: Span) -> IResult<Span, InterfaceIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, InterfaceIdentifier { nodes: (a,) }))
}

#[parser]
pub fn interface_instance_identifier(s: Span) -> IResult<Span, InterfaceInstanceIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, InterfaceInstanceIdentifier { nodes: (a,) }))
}

#[parser]
pub fn inout_port_identifier(s: Span) -> IResult<Span, InoutPortIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, InoutPortIdentifier { nodes: (a,) }))
}

#[parser]
pub fn input_port_identifier(s: Span) -> IResult<Span, InputPortIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, InputPortIdentifier { nodes: (a,) }))
}

#[parser]
pub fn instance_identifier(s: Span) -> IResult<Span, InstanceIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, InstanceIdentifier { nodes: (a,) }))
}

#[parser]
pub fn library_identifier(s: Span) -> IResult<Span, LibraryIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, LibraryIdentifier { nodes: (a,) }))
}

#[parser]
pub fn member_identifier(s: Span) -> IResult<Span, MemberIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, MemberIdentifier { nodes: (a,) }))
}

#[parser]
pub fn method_identifier(s: Span) -> IResult<Span, MethodIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, MethodIdentifier { nodes: (a,) }))
}

#[parser]
pub fn modport_identifier(s: Span) -> IResult<Span, ModportIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ModportIdentifier { nodes: (a,) }))
}

#[parser]
pub fn module_identifier(s: Span) -> IResult<Span, ModuleIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ModuleIdentifier { nodes: (a,) }))
}

#[parser]
pub fn net_identifier(s: Span) -> IResult<Span, NetIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, NetIdentifier { nodes: (a,) }))
}

#[parser]
pub fn net_type_identifier(s: Span) -> IResult<Span, NetTypeIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, NetTypeIdentifier { nodes: (a,) }))
}

#[parser]
pub fn output_port_identifier(s: Span) -> IResult<Span, OutputPortIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, OutputPortIdentifier { nodes: (a,) }))
}

#[parser]
pub fn package_identifier(s: Span) -> IResult<Span, PackageIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, PackageIdentifier { nodes: (a,) }))
}

#[packrat_parser]
#[parser]
pub fn package_scope(s: Span) -> IResult<Span, PackageScope> {
    alt((
        package_scope_package,
        map(unit, |x| PackageScope::Unit(Box::new(x))),
    ))(s)
}

#[parser]
pub fn package_scope_package(s: Span) -> IResult<Span, PackageScope> {
    let (s, a) = package_identifier(s)?;
    let (s, b) = symbol("::")(s)?;
    Ok((
        s,
        PackageScope::Package(Box::new(PackageScopePackage { nodes: (a, b) })),
    ))
}

#[parser]
pub fn unit(s: Span) -> IResult<Span, Unit> {
    let (s, a) = keyword("$unit")(s)?;
    let (s, b) = symbol("::")(s)?;
    Ok((s, Unit { nodes: (a, b) }))
}

#[parser]
pub fn parameter_identifier(s: Span) -> IResult<Span, ParameterIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ParameterIdentifier { nodes: (a,) }))
}

#[parser]
pub fn port_identifier(s: Span) -> IResult<Span, PortIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, PortIdentifier { nodes: (a,) }))
}

#[parser]
pub fn production_identifier(s: Span) -> IResult<Span, ProductionIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ProductionIdentifier { nodes: (a,) }))
}

#[parser]
pub fn program_identifier(s: Span) -> IResult<Span, ProgramIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ProgramIdentifier { nodes: (a,) }))
}

#[parser]
pub fn property_identifier(s: Span) -> IResult<Span, PropertyIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, PropertyIdentifier { nodes: (a,) }))
}

#[parser]
pub fn ps_class_identifier(s: Span) -> IResult<Span, PsClassIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = class_identifier(s)?;
    Ok((s, PsClassIdentifier { nodes: (a, b) }))
}

#[parser]
pub fn ps_covergroup_identifier(s: Span) -> IResult<Span, PsCovergroupIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = covergroup_identifier(s)?;
    Ok((s, PsCovergroupIdentifier { nodes: (a, b) }))
}

#[parser]
pub fn ps_checker_identifier(s: Span) -> IResult<Span, PsCheckerIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = checker_identifier(s)?;
    Ok((s, PsCheckerIdentifier { nodes: (a, b) }))
}

#[parser]
pub fn ps_identifier(s: Span) -> IResult<Span, PsIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = identifier(s)?;
    Ok((s, PsIdentifier { nodes: (a, b) }))
}

#[parser]
pub fn ps_or_hierarchical_array_identifier(
    s: Span,
) -> IResult<Span, PsOrHierarchicalArrayIdentifier> {
    let (s, a) = opt(implicit_class_handle_or_class_scope_or_package_scope)(s)?;
    let (s, b) = hierarchical_array_identifier(s)?;
    Ok((s, PsOrHierarchicalArrayIdentifier { nodes: (a, b) }))
}

#[parser]
pub fn ps_or_hierarchical_net_identifier(s: Span) -> IResult<Span, PsOrHierarchicalNetIdentifier> {
    alt((
        ps_or_hierarchical_net_identifier_package_scope,
        map(hierarchical_net_identifier, |x| {
            PsOrHierarchicalNetIdentifier::HierarchicalNetIdentifier(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn ps_or_hierarchical_net_identifier_package_scope(
    s: Span,
) -> IResult<Span, PsOrHierarchicalNetIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = net_identifier(s)?;
    Ok((
        s,
        PsOrHierarchicalNetIdentifier::PackageScope(Box::new(
            PsOrHierarchicalNetIdentifierPackageScope { nodes: (a, b) },
        )),
    ))
}

#[parser]
pub fn ps_or_hierarchical_property_identifier(
    s: Span,
) -> IResult<Span, PsOrHierarchicalPropertyIdentifier> {
    alt((
        ps_or_hierarchical_property_identifier_package_scope,
        map(hierarchical_property_identifier, |x| {
            PsOrHierarchicalPropertyIdentifier::HierarchicalPropertyIdentifier(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn ps_or_hierarchical_property_identifier_package_scope(
    s: Span,
) -> IResult<Span, PsOrHierarchicalPropertyIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = property_identifier(s)?;
    Ok((
        s,
        PsOrHierarchicalPropertyIdentifier::PackageScope(Box::new(
            PsOrHierarchicalPropertyIdentifierPackageScope { nodes: (a, b) },
        )),
    ))
}

#[parser]
pub fn ps_or_hierarchical_sequence_identifier(
    s: Span,
) -> IResult<Span, PsOrHierarchicalSequenceIdentifier> {
    alt((
        ps_or_hierarchical_sequence_identifier_package_scope,
        map(hierarchical_sequence_identifier, |x| {
            PsOrHierarchicalSequenceIdentifier::HierarchicalSequenceIdentifier(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn ps_or_hierarchical_sequence_identifier_package_scope(
    s: Span,
) -> IResult<Span, PsOrHierarchicalSequenceIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = sequence_identifier(s)?;
    Ok((
        s,
        PsOrHierarchicalSequenceIdentifier::PackageScope(Box::new(
            PsOrHierarchicalSequenceIdentifierPackageScope { nodes: (a, b) },
        )),
    ))
}

#[parser]
pub fn ps_or_hierarchical_tf_identifier(s: Span) -> IResult<Span, PsOrHierarchicalTfIdentifier> {
    alt((
        ps_or_hierarchical_tf_identifier_package_scope,
        map(hierarchical_tf_identifier, |x| {
            PsOrHierarchicalTfIdentifier::HierarchicalTfIdentifier(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn ps_or_hierarchical_tf_identifier_package_scope(
    s: Span,
) -> IResult<Span, PsOrHierarchicalTfIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = tf_identifier(s)?;
    Ok((
        s,
        PsOrHierarchicalTfIdentifier::PackageScope(Box::new(
            PsOrHierarchicalTfIdentifierPackageScope { nodes: (a, b) },
        )),
    ))
}

#[packrat_parser]
#[parser]
pub fn ps_parameter_identifier(s: Span) -> IResult<Span, PsParameterIdentifier> {
    alt((
        ps_parameter_identifier_scope,
        ps_parameter_identifier_generate,
    ))(s)
}

#[parser]
pub fn ps_parameter_identifier_scope(s: Span) -> IResult<Span, PsParameterIdentifier> {
    let (s, a) = opt(package_scope_or_class_scope)(s)?;
    let (s, b) = parameter_identifier(s)?;
    Ok((
        s,
        PsParameterIdentifier::Scope(Box::new(PsParameterIdentifierScope { nodes: (a, b) })),
    ))
}

#[parser]
pub fn ps_parameter_identifier_generate(s: Span) -> IResult<Span, PsParameterIdentifier> {
    let (s, a) = many0(triple(
        generate_block_identifier,
        opt(bracket(constant_expression)),
        symbol("."),
    ))(s)?;
    let (s, b) = parameter_identifier(s)?;
    Ok((
        s,
        PsParameterIdentifier::Generate(Box::new(PsParameterIdentifierGenerate { nodes: (a, b) })),
    ))
}

#[packrat_parser]
#[parser]
pub fn ps_type_identifier(s: Span) -> IResult<Span, PsTypeIdentifier> {
    let (s, a) = opt(local_or_package_scope_or_class_scope)(s)?;
    let (s, b) = type_identifier(s)?;
    Ok((s, PsTypeIdentifier { nodes: (a, b) }))
}

#[parser]
pub fn sequence_identifier(s: Span) -> IResult<Span, SequenceIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, SequenceIdentifier { nodes: (a,) }))
}

#[parser]
pub fn signal_identifier(s: Span) -> IResult<Span, SignalIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, SignalIdentifier { nodes: (a,) }))
}

#[parser]
pub fn simple_identifier(s: Span) -> IResult<Span, SimpleIdentifier> {
    let (s, a) = ws(simple_identifier_impl)(s)?;
    Ok((s, SimpleIdentifier { nodes: a }))
}

#[parser]
pub fn simple_identifier_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = is_a(AZ_)(s)?;
    let (s, b) = opt(is_a(AZ09_DOLLAR))(s)?;
    let a = if let Some(b) = b {
        concat(a, b).unwrap()
    } else {
        a
    };
    if is_keyword(&a) {
        Err(Err::Error(make_error(s, ErrorKind::Fix)))
    } else {
        Ok((s, a.into()))
    }
}

#[parser]
pub fn specparam_identifier(s: Span) -> IResult<Span, SpecparamIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, SpecparamIdentifier { nodes: (a,) }))
}

#[parser]
pub fn system_tf_identifier(s: Span) -> IResult<Span, SystemTfIdentifier> {
    let (s, a) = ws(system_tf_identifier_impl)(s)?;
    Ok((s, SystemTfIdentifier { nodes: a }))
}

#[parser]
pub fn system_tf_identifier_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = tag("$")(s)?;
    let (s, b) = is_a(AZ09_DOLLAR)(s)?;
    let a = concat(a, b).unwrap();
    Ok((s, a.into()))
}

#[parser]
pub fn task_identifier(s: Span) -> IResult<Span, TaskIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TaskIdentifier { nodes: (a,) }))
}

#[parser]
pub fn tf_identifier(s: Span) -> IResult<Span, TfIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TfIdentifier { nodes: (a,) }))
}

#[parser]
pub fn terminal_identifier(s: Span) -> IResult<Span, TerminalIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TerminalIdentifier { nodes: (a,) }))
}

#[parser]
pub fn topmodule_identifier(s: Span) -> IResult<Span, TopmoduleIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TopmoduleIdentifier { nodes: (a,) }))
}

#[parser]
pub fn type_identifier(s: Span) -> IResult<Span, TypeIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TypeIdentifier { nodes: (a,) }))
}

#[parser]
pub fn udp_identifier(s: Span) -> IResult<Span, UdpIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, UdpIdentifier { nodes: (a,) }))
}

#[packrat_parser]
#[parser]
pub fn variable_identifier(s: Span) -> IResult<Span, VariableIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, VariableIdentifier { nodes: (a,) }))
}

#[parser]
pub fn implicit_class_handle_or_class_scope_or_package_scope(
    s: Span,
) -> IResult<Span, ImplicitClassHandleOrClassScopeOrPackageScope> {
    alt((
        map(pair(implicit_class_handle, symbol(".")), |x| {
            ImplicitClassHandleOrClassScopeOrPackageScope::ImplicitClassHandle(Box::new(x))
        }),
        map(class_scope, |x| {
            ImplicitClassHandleOrClassScopeOrPackageScope::ClassScope(Box::new(x))
        }),
        map(package_scope, |x| {
            ImplicitClassHandleOrClassScopeOrPackageScope::PackageScope(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn implicit_class_handle_or_package_scope(
    s: Span,
) -> IResult<Span, ImplicitClassHandleOrPackageScope> {
    alt((
        map(pair(implicit_class_handle, symbol(".")), |x| {
            ImplicitClassHandleOrPackageScope::ImplicitClassHandle(Box::new(x))
        }),
        map(package_scope, |x| {
            ImplicitClassHandleOrPackageScope::PackageScope(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn implicit_class_handle_or_class_scope(
    s: Span,
) -> IResult<Span, ImplicitClassHandleOrClassScope> {
    alt((
        map(pair(implicit_class_handle, symbol(".")), |x| {
            ImplicitClassHandleOrClassScope::ImplicitClassHandle(Box::new(x))
        }),
        map(class_scope, |x| {
            ImplicitClassHandleOrClassScope::ClassScope(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn package_scope_or_class_scope(s: Span) -> IResult<Span, PackageScopeOrClassScope> {
    alt((
        map(package_scope, |x| {
            PackageScopeOrClassScope::PackageScope(Box::new(x))
        }),
        map(class_scope, |x| {
            PackageScopeOrClassScope::ClassScope(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn local_or_package_scope_or_class_scope(
    s: Span,
) -> IResult<Span, LocalOrPackageScopeOrClassScope> {
    alt((
        map(local, |x| {
            LocalOrPackageScopeOrClassScope::Local(Box::new(x))
        }),
        map(package_scope, |x| {
            LocalOrPackageScopeOrClassScope::PackageScope(Box::new(x))
        }),
        map(class_scope, |x| {
            LocalOrPackageScopeOrClassScope::ClassScope(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn local(s: Span) -> IResult<Span, Local> {
    let (s, a) = keyword("local")(s)?;
    let (s, b) = symbol("::")(s)?;
    Ok((s, Local { nodes: (a, b) }))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_identifier() {
        parser_test!(
            identifier,
            "shiftreg_a",
            Ok((_, Identifier::SimpleIdentifier(_)))
        );
        parser_test!(
            identifier,
            "_bus3",
            Ok((_, Identifier::SimpleIdentifier(_)))
        );
        parser_test!(
            identifier,
            "n$657",
            Ok((_, Identifier::SimpleIdentifier(_)))
        );
        parser_test!(
            identifier,
            "\\busa+index",
            Ok((_, Identifier::EscapedIdentifier(_)))
        );
        parser_test!(
            identifier,
            "\\-clock",
            Ok((_, Identifier::EscapedIdentifier(_)))
        );
    }

    #[test]
    fn test_system_tf_identifier() {
        parser_test!(system_tf_identifier, "$display", Ok((_, _)));
    }
}
