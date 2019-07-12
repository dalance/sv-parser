use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::bytes::complete::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

const AZ_: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_";
const AZ09_: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_";
const AZ09_DOLLAR: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_$";

#[derive(Debug, Node)]
pub struct ArrayIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct BlockIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct BinIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct CIdentifier<'a> {
    pub nodes: (Span<'a>, Vec<WhiteSpace<'a>>),
}

#[derive(Debug, Node)]
pub struct CellIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct CheckerIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct ClassIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct ClassVariableIdentifier<'a> {
    pub nodes: (VariableIdentifier<'a>,),
}

#[derive(Debug, Node)]
pub struct ClockingIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct ConfigIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct ConstIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct ConstraintIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct CovergroupIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct CovergroupVariableIdentifier<'a> {
    pub nodes: (VariableIdentifier<'a>,),
}

#[derive(Debug, Node)]
pub struct CoverPointIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct CrossIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct DynamicArrayVariableIdentifier<'a> {
    pub nodes: (VariableIdentifier<'a>,),
}

#[derive(Debug, Node)]
pub struct EnumIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct EscapedIdentifier<'a> {
    pub nodes: (Span<'a>, Vec<WhiteSpace<'a>>),
}

#[derive(Debug, Node)]
pub struct FormalIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct FormalPortIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct FunctionIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct GenerateBlockIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct GenvarIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct HierarchicalArrayIdentifier<'a> {
    pub nodes: (HierarchicalIdentifier<'a>,),
}

#[derive(Debug)]
pub struct HierarchicalBlockIdentifier<'a> {
    pub nodes: (HierarchicalIdentifier<'a>,),
}

#[derive(Debug)]
pub struct HierarchicalEventIdentifier<'a> {
    pub nodes: (HierarchicalIdentifier<'a>,),
}

#[derive(Debug)]
pub struct HierarchicalIdentifier<'a> {
    pub nodes: (
        Option<Root<'a>>,
        Vec<(Identifier<'a>, ConstantBitSelect<'a>, Symbol<'a>)>,
        Identifier<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct Root<'a> {
    pub nodes: (Symbol<'a>, Symbol<'a>),
}

#[derive(Debug)]
pub struct HierarchicalNetIdentifier<'a> {
    pub nodes: (HierarchicalIdentifier<'a>,),
}

#[derive(Debug)]
pub struct HierarchicalParameterIdentifier<'a> {
    pub nodes: (HierarchicalIdentifier<'a>,),
}

#[derive(Debug)]
pub struct HierarchicalPropertyIdentifier<'a> {
    pub nodes: (HierarchicalIdentifier<'a>,),
}

#[derive(Debug)]
pub struct HierarchicalSequenceIdentifier<'a> {
    pub nodes: (HierarchicalIdentifier<'a>,),
}

#[derive(Debug)]
pub struct HierarchicalTaskIdentifier<'a> {
    pub nodes: (HierarchicalIdentifier<'a>,),
}

#[derive(Debug)]
pub struct HierarchicalTfIdentifier<'a> {
    pub nodes: (HierarchicalIdentifier<'a>,),
}

#[derive(Debug)]
pub struct HierarchicalVariableIdentifier<'a> {
    pub nodes: (HierarchicalIdentifier<'a>,),
}

#[derive(Debug, Node)]
pub enum Identifier<'a> {
    SimpleIdentifier(SimpleIdentifier<'a>),
    EscapedIdentifier(EscapedIdentifier<'a>),
}

#[derive(Debug, Node)]
pub struct IndexVariableIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct InterfaceIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct InterfaceInstanceIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct InoutPortIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct InputPortIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct InstanceIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct LibraryIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct MemberIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct MethodIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct ModportIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct ModuleIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct NetIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct NetTypeIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct OutputPortIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct PackageIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub enum PackageScope<'a> {
    Package(PackageScopePackage<'a>),
    Unit(Unit<'a>),
}

#[derive(Debug, Node)]
pub struct PackageScopePackage<'a> {
    pub nodes: (PackageIdentifier<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct Unit<'a> {
    pub nodes: (Symbol<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct ParameterIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct PortIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct ProductionIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct ProgramIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct PropertyIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct PsClassIdentifier<'a> {
    pub nodes: (Option<PackageScope<'a>>, ClassIdentifier<'a>),
}

#[derive(Debug, Node)]
pub struct PsCovergroupIdentifier<'a> {
    pub nodes: (Option<PackageScope<'a>>, CovergroupIdentifier<'a>),
}

#[derive(Debug, Node)]
pub struct PsCheckerIdentifier<'a> {
    pub nodes: (Option<PackageScope<'a>>, CheckerIdentifier<'a>),
}

#[derive(Debug, Node)]
pub struct PsIdentifier<'a> {
    pub nodes: (Option<PackageScope<'a>>, Identifier<'a>),
}

#[derive(Debug)]
pub struct PsOrHierarchicalArrayIdentifier<'a> {
    pub nodes: (
        Option<ImplicitClassHandleOrClassScopeOrPackageScope<'a>>,
        HierarchicalArrayIdentifier<'a>,
    ),
}

#[derive(Debug)]
pub enum PsOrHierarchicalNetIdentifier<'a> {
    PackageScope(PsOrHierarchicalNetIdentifierPackageScope<'a>),
    HierarchicalNetIdentifier(HierarchicalNetIdentifier<'a>),
}

#[derive(Debug, Node)]
pub struct PsOrHierarchicalNetIdentifierPackageScope<'a> {
    pub nodes: (Option<PackageScope<'a>>, NetIdentifier<'a>),
}

#[derive(Debug)]
pub struct PsOrHierarchicalNetIdentifierHierarchical<'a> {
    pub nodes: (HierarchicalNetIdentifier<'a>),
}

#[derive(Debug)]
pub enum PsOrHierarchicalPropertyIdentifier<'a> {
    PackageScope(PsOrHierarchicalPropertyIdentifierPackageScope<'a>),
    HierarchicalPropertyIdentifier(HierarchicalPropertyIdentifier<'a>),
}

#[derive(Debug)]
pub struct PsOrHierarchicalPropertyIdentifierPackageScope<'a> {
    pub nodes: (Option<PackageScope<'a>>, PropertyIdentifier<'a>),
}

#[derive(Debug)]
pub struct PsOrHierarchicalPropertyIdentifierHierarchical<'a> {
    pub nodes: (HierarchicalPropertyIdentifier<'a>),
}

#[derive(Debug)]
pub enum PsOrHierarchicalSequenceIdentifier<'a> {
    PackageScope(PsOrHierarchicalSequenceIdentifierPackageScope<'a>),
    HierarchicalSequenceIdentifier(HierarchicalSequenceIdentifier<'a>),
}

#[derive(Debug)]
pub struct PsOrHierarchicalSequenceIdentifierPackageScope<'a> {
    pub nodes: (Option<PackageScope<'a>>, SequenceIdentifier<'a>),
}

#[derive(Debug)]
pub struct PsOrHierarchicalSequenceIdentifierHierarchical<'a> {
    pub nodes: (HierarchicalSequenceIdentifier<'a>),
}

#[derive(Debug)]
pub enum PsOrHierarchicalTfIdentifier<'a> {
    PackageScope(PsOrHierarchicalTfIdentifierPackageScope<'a>),
    HierarchicalTfIdentifier(HierarchicalTfIdentifier<'a>),
}

#[derive(Debug)]
pub struct PsOrHierarchicalTfIdentifierPackageScope<'a> {
    pub nodes: (Option<PackageScope<'a>>, TfIdentifier<'a>),
}

#[derive(Debug)]
pub struct PsOrHierarchicalTfIdentifierHierarchical<'a> {
    pub nodes: (HierarchicalTfIdentifier<'a>),
}

#[derive(Debug)]
pub enum PsParameterIdentifier<'a> {
    Scope(PsParameterIdentifierScope<'a>),
    Generate(PsParameterIdentifierGenerate<'a>),
}

#[derive(Debug)]
pub struct PsParameterIdentifierScope<'a> {
    pub nodes: (
        Option<PackageScopeOrClassScope<'a>>,
        ParameterIdentifier<'a>,
    ),
}

#[derive(Debug)]
pub struct PsParameterIdentifierGenerate<'a> {
    pub nodes: (
        Vec<(
            GenerateBlockIdentifier<'a>,
            Option<Bracket<'a, ConstantExpression<'a>>>,
            Symbol<'a>,
        )>,
        ParameterIdentifier<'a>,
    ),
}

#[derive(Debug)]
pub struct PsTypeIdentifier<'a> {
    pub nodes: (
        Option<LocalOrPackageScopeOrClassScope<'a>>,
        TypeIdentifier<'a>,
    ),
}

#[derive(Debug)]
pub enum LocalOrPackageScopeOrClassScope<'a> {
    Local(Local<'a>),
    PackageScope(PackageScope<'a>),
    ClassScope(ClassScope<'a>),
}

#[derive(Debug, Node)]
pub struct Local<'a> {
    pub nodes: (Symbol<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct SequenceIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct SignalIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct SimpleIdentifier<'a> {
    pub nodes: (Span<'a>, Vec<WhiteSpace<'a>>),
}

#[derive(Debug, Node)]
pub struct SpecparamIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct SystemTfIdentifier<'a> {
    pub nodes: (Span<'a>, Vec<WhiteSpace<'a>>),
}

#[derive(Debug, Node)]
pub struct TaskIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct TfIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct TerminalIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct TopmoduleIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct TypeIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct UdpIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct VariableIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub enum ImplicitClassHandleOrClassScopeOrPackageScope<'a> {
    ImplicitClassHandle((ImplicitClassHandle<'a>, Symbol<'a>)),
    ClassScope(ClassScope<'a>),
    PackageScope(PackageScope<'a>),
}

#[derive(Debug)]
pub enum ImplicitClassHandleOrPackageScope<'a> {
    ImplicitClassHandle((ImplicitClassHandle<'a>, Symbol<'a>)),
    PackageScope(PackageScope<'a>),
}

#[derive(Debug)]
pub enum ImplicitClassHandleOrClassScope<'a> {
    ImplicitClassHandle((ImplicitClassHandle<'a>, Symbol<'a>)),
    ClassScope(ClassScope<'a>),
}

#[derive(Debug)]
pub enum PackageScopeOrClassScope<'a> {
    PackageScope(PackageScope<'a>),
    ClassScope(ClassScope<'a>),
}

// -----------------------------------------------------------------------------

pub fn array_identifier(s: Span) -> IResult<Span, ArrayIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ArrayIdentifier { nodes: (a,) }))
}

pub fn block_identifier(s: Span) -> IResult<Span, BlockIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, BlockIdentifier { nodes: (a,) }))
}

pub fn bin_identifier(s: Span) -> IResult<Span, BinIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, BinIdentifier { nodes: (a,) }))
}

pub fn c_identifier(s: Span) -> IResult<Span, CIdentifier> {
    let (s, a) = ws(c_identifier_impl)(s)?;
    Ok((s, CIdentifier { nodes: a }))
}

pub fn c_identifier_impl(s: Span) -> IResult<Span, Span> {
    let (s, a) = is_a(AZ_)(s)?;
    let (s, b) = opt(is_a(AZ09_))(s)?;
    let a = if let Some(b) = b {
        concat(a, b).unwrap()
    } else {
        a
    };
    Ok((s, a))
}

pub fn cell_identifier(s: Span) -> IResult<Span, CellIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, CellIdentifier { nodes: (a,) }))
}

pub fn checker_identifier(s: Span) -> IResult<Span, CheckerIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, CheckerIdentifier { nodes: (a,) }))
}

pub fn class_identifier(s: Span) -> IResult<Span, ClassIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ClassIdentifier { nodes: (a,) }))
}

pub fn class_variable_identifier(s: Span) -> IResult<Span, ClassVariableIdentifier> {
    let (s, a) = variable_identifier(s)?;
    Ok((s, ClassVariableIdentifier { nodes: (a,) }))
}

pub fn clocking_identifier(s: Span) -> IResult<Span, ClockingIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ClockingIdentifier { nodes: (a,) }))
}

pub fn config_identifier(s: Span) -> IResult<Span, ConfigIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ConfigIdentifier { nodes: (a,) }))
}

pub fn const_identifier(s: Span) -> IResult<Span, ConstIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ConstIdentifier { nodes: (a,) }))
}

pub fn constraint_identifier(s: Span) -> IResult<Span, ConstraintIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ConstraintIdentifier { nodes: (a,) }))
}

pub fn covergroup_identifier(s: Span) -> IResult<Span, CovergroupIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, CovergroupIdentifier { nodes: (a,) }))
}

pub fn covergroup_variable_identifier(s: Span) -> IResult<Span, CovergroupVariableIdentifier> {
    let (s, a) = variable_identifier(s)?;
    Ok((s, CovergroupVariableIdentifier { nodes: (a,) }))
}

pub fn cover_point_identifier(s: Span) -> IResult<Span, CoverPointIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, CoverPointIdentifier { nodes: (a,) }))
}

pub fn cross_identifier(s: Span) -> IResult<Span, CrossIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, CrossIdentifier { nodes: (a,) }))
}

pub fn dynamic_array_variable_identifier(s: Span) -> IResult<Span, DynamicArrayVariableIdentifier> {
    let (s, a) = variable_identifier(s)?;
    Ok((s, DynamicArrayVariableIdentifier { nodes: (a,) }))
}

pub fn enum_identifier(s: Span) -> IResult<Span, EnumIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, EnumIdentifier { nodes: (a,) }))
}

pub fn escaped_identifier(s: Span) -> IResult<Span, EscapedIdentifier> {
    let (s, a) = ws(escaped_identifier_impl)(s)?;
    Ok((s, EscapedIdentifier { nodes: a }))
}

pub fn escaped_identifier_impl(s: Span) -> IResult<Span, Span> {
    let (s, a) = tag("\\")(s)?;
    let (s, b) = is_not(" \t\r\n")(s)?;
    let a = concat(a, b).unwrap();
    Ok((s, a))
}

pub fn formal_identifier(s: Span) -> IResult<Span, FormalIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, FormalIdentifier { nodes: (a,) }))
}

pub fn formal_port_identifier(s: Span) -> IResult<Span, FormalPortIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, FormalPortIdentifier { nodes: (a,) }))
}

pub fn function_identifier(s: Span) -> IResult<Span, FunctionIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, FunctionIdentifier { nodes: (a,) }))
}

pub fn generate_block_identifier(s: Span) -> IResult<Span, GenerateBlockIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, GenerateBlockIdentifier { nodes: (a,) }))
}

pub fn genvar_identifier(s: Span) -> IResult<Span, GenvarIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, GenvarIdentifier { nodes: (a,) }))
}

pub fn hierarchical_array_identifier(s: Span) -> IResult<Span, HierarchicalArrayIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalArrayIdentifier { nodes: (a,) }))
}

pub fn hierarchical_block_identifier(s: Span) -> IResult<Span, HierarchicalBlockIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalBlockIdentifier { nodes: (a,) }))
}

pub fn hierarchical_event_identifier(s: Span) -> IResult<Span, HierarchicalEventIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalEventIdentifier { nodes: (a,) }))
}

pub fn hierarchical_identifier(s: Span) -> IResult<Span, HierarchicalIdentifier> {
    let (s, a) = opt(root)(s)?;
    let (s, b) = many0(triple(identifier, constant_bit_select, symbol(".")))(s)?;
    let (s, c) = identifier(s)?;
    Ok((s, HierarchicalIdentifier { nodes: (a, b, c) }))
}

pub fn root(s: Span) -> IResult<Span, Root> {
    let (s, a) = symbol("$root")(s)?;
    let (s, b) = symbol(".")(s)?;
    Ok((s, Root { nodes: (a, b) }))
}

pub fn hierarchical_net_identifier(s: Span) -> IResult<Span, HierarchicalNetIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalNetIdentifier { nodes: (a,) }))
}

pub fn hierarchical_parameter_identifier(
    s: Span,
) -> IResult<Span, HierarchicalParameterIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalParameterIdentifier { nodes: (a,) }))
}

pub fn hierarchical_property_identifier(s: Span) -> IResult<Span, HierarchicalPropertyIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalPropertyIdentifier { nodes: (a,) }))
}

pub fn hierarchical_sequence_identifier(s: Span) -> IResult<Span, HierarchicalSequenceIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalSequenceIdentifier { nodes: (a,) }))
}

pub fn hierarchical_task_identifier(s: Span) -> IResult<Span, HierarchicalTaskIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalTaskIdentifier { nodes: (a,) }))
}

pub fn hierarchical_tf_identifier(s: Span) -> IResult<Span, HierarchicalTfIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalTfIdentifier { nodes: (a,) }))
}

pub fn hierarchical_variable_identifier(s: Span) -> IResult<Span, HierarchicalVariableIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalVariableIdentifier { nodes: (a,) }))
}

pub fn identifier(s: Span) -> IResult<Span, Identifier> {
    alt((
        map(escaped_identifier, |x| Identifier::EscapedIdentifier(x)),
        map(simple_identifier, |x| Identifier::SimpleIdentifier(x)),
    ))(s)
}

pub fn index_variable_identifier(s: Span) -> IResult<Span, IndexVariableIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, IndexVariableIdentifier { nodes: (a,) }))
}

pub fn interface_identifier(s: Span) -> IResult<Span, InterfaceIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, InterfaceIdentifier { nodes: (a,) }))
}

pub fn interface_instance_identifier(s: Span) -> IResult<Span, InterfaceInstanceIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, InterfaceInstanceIdentifier { nodes: (a,) }))
}

pub fn inout_port_identifier(s: Span) -> IResult<Span, InoutPortIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, InoutPortIdentifier { nodes: (a,) }))
}

pub fn input_port_identifier(s: Span) -> IResult<Span, InputPortIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, InputPortIdentifier { nodes: (a,) }))
}

pub fn instance_identifier(s: Span) -> IResult<Span, InstanceIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, InstanceIdentifier { nodes: (a,) }))
}

pub fn library_identifier(s: Span) -> IResult<Span, LibraryIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, LibraryIdentifier { nodes: (a,) }))
}

pub fn member_identifier(s: Span) -> IResult<Span, MemberIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, MemberIdentifier { nodes: (a,) }))
}

pub fn method_identifier(s: Span) -> IResult<Span, MethodIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, MethodIdentifier { nodes: (a,) }))
}

pub fn modport_identifier(s: Span) -> IResult<Span, ModportIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ModportIdentifier { nodes: (a,) }))
}

pub fn module_identifier(s: Span) -> IResult<Span, ModuleIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ModuleIdentifier { nodes: (a,) }))
}

pub fn net_identifier(s: Span) -> IResult<Span, NetIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, NetIdentifier { nodes: (a,) }))
}

pub fn net_type_identifier(s: Span) -> IResult<Span, NetTypeIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, NetTypeIdentifier { nodes: (a,) }))
}

pub fn output_port_identifier(s: Span) -> IResult<Span, OutputPortIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, OutputPortIdentifier { nodes: (a,) }))
}

pub fn package_identifier(s: Span) -> IResult<Span, PackageIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, PackageIdentifier { nodes: (a,) }))
}

pub fn package_scope(s: Span) -> IResult<Span, PackageScope> {
    alt((package_scope_package, map(unit, |x| PackageScope::Unit(x))))(s)
}

pub fn package_scope_package(s: Span) -> IResult<Span, PackageScope> {
    let (s, a) = package_identifier(s)?;
    let (s, b) = symbol("::")(s)?;
    Ok((
        s,
        PackageScope::Package(PackageScopePackage { nodes: (a, b) }),
    ))
}

pub fn unit(s: Span) -> IResult<Span, Unit> {
    let (s, a) = symbol("$unit")(s)?;
    let (s, b) = symbol("::")(s)?;
    Ok((s, Unit { nodes: (a, b) }))
}

pub fn parameter_identifier(s: Span) -> IResult<Span, ParameterIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ParameterIdentifier { nodes: (a,) }))
}

pub fn port_identifier(s: Span) -> IResult<Span, PortIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, PortIdentifier { nodes: (a,) }))
}

pub fn production_identifier(s: Span) -> IResult<Span, ProductionIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ProductionIdentifier { nodes: (a,) }))
}

pub fn program_identifier(s: Span) -> IResult<Span, ProgramIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ProgramIdentifier { nodes: (a,) }))
}

pub fn property_identifier(s: Span) -> IResult<Span, PropertyIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, PropertyIdentifier { nodes: (a,) }))
}

pub fn ps_class_identifier(s: Span) -> IResult<Span, PsClassIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = class_identifier(s)?;
    Ok((s, PsClassIdentifier { nodes: (a, b) }))
}

pub fn ps_covergroup_identifier(s: Span) -> IResult<Span, PsCovergroupIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = covergroup_identifier(s)?;
    Ok((s, PsCovergroupIdentifier { nodes: (a, b) }))
}

pub fn ps_checker_identifier(s: Span) -> IResult<Span, PsCheckerIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = checker_identifier(s)?;
    Ok((s, PsCheckerIdentifier { nodes: (a, b) }))
}

pub fn ps_identifier(s: Span) -> IResult<Span, PsIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = identifier(s)?;
    Ok((s, PsIdentifier { nodes: (a, b) }))
}

pub fn ps_or_hierarchical_array_identifier(
    s: Span,
) -> IResult<Span, PsOrHierarchicalArrayIdentifier> {
    let (s, a) = opt(implicit_class_handle_or_class_scope_or_package_scope)(s)?;
    let (s, b) = hierarchical_array_identifier(s)?;
    Ok((s, PsOrHierarchicalArrayIdentifier { nodes: (a, b) }))
}

pub fn ps_or_hierarchical_net_identifier(s: Span) -> IResult<Span, PsOrHierarchicalNetIdentifier> {
    alt((
        ps_or_hierarchical_net_identifier_package_scope,
        map(hierarchical_net_identifier, |x| {
            PsOrHierarchicalNetIdentifier::HierarchicalNetIdentifier(x)
        }),
    ))(s)
}

pub fn ps_or_hierarchical_net_identifier_package_scope(
    s: Span,
) -> IResult<Span, PsOrHierarchicalNetIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = net_identifier(s)?;
    Ok((
        s,
        PsOrHierarchicalNetIdentifier::PackageScope(PsOrHierarchicalNetIdentifierPackageScope {
            nodes: (a, b),
        }),
    ))
}

pub fn ps_or_hierarchical_property_identifier(
    s: Span,
) -> IResult<Span, PsOrHierarchicalPropertyIdentifier> {
    alt((
        ps_or_hierarchical_property_identifier_package_scope,
        map(hierarchical_property_identifier, |x| {
            PsOrHierarchicalPropertyIdentifier::HierarchicalPropertyIdentifier(x)
        }),
    ))(s)
}

pub fn ps_or_hierarchical_property_identifier_package_scope(
    s: Span,
) -> IResult<Span, PsOrHierarchicalPropertyIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = property_identifier(s)?;
    Ok((
        s,
        PsOrHierarchicalPropertyIdentifier::PackageScope(
            PsOrHierarchicalPropertyIdentifierPackageScope { nodes: (a, b) },
        ),
    ))
}

pub fn ps_or_hierarchical_sequence_identifier(
    s: Span,
) -> IResult<Span, PsOrHierarchicalSequenceIdentifier> {
    alt((
        ps_or_hierarchical_sequence_identifier_package_scope,
        map(hierarchical_sequence_identifier, |x| {
            PsOrHierarchicalSequenceIdentifier::HierarchicalSequenceIdentifier(x)
        }),
    ))(s)
}

pub fn ps_or_hierarchical_sequence_identifier_package_scope(
    s: Span,
) -> IResult<Span, PsOrHierarchicalSequenceIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = sequence_identifier(s)?;
    Ok((
        s,
        PsOrHierarchicalSequenceIdentifier::PackageScope(
            PsOrHierarchicalSequenceIdentifierPackageScope { nodes: (a, b) },
        ),
    ))
}

pub fn ps_or_hierarchical_tf_identifier(s: Span) -> IResult<Span, PsOrHierarchicalTfIdentifier> {
    alt((
        ps_or_hierarchical_tf_identifier_package_scope,
        map(hierarchical_tf_identifier, |x| {
            PsOrHierarchicalTfIdentifier::HierarchicalTfIdentifier(x)
        }),
    ))(s)
}

pub fn ps_or_hierarchical_tf_identifier_package_scope(
    s: Span,
) -> IResult<Span, PsOrHierarchicalTfIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = tf_identifier(s)?;
    Ok((
        s,
        PsOrHierarchicalTfIdentifier::PackageScope(PsOrHierarchicalTfIdentifierPackageScope {
            nodes: (a, b),
        }),
    ))
}

pub fn ps_parameter_identifier(s: Span) -> IResult<Span, PsParameterIdentifier> {
    alt((
        ps_parameter_identifier_scope,
        ps_parameter_identifier_generate,
    ))(s)
}

pub fn ps_parameter_identifier_scope(s: Span) -> IResult<Span, PsParameterIdentifier> {
    let (s, a) = opt(package_scope_or_class_scope)(s)?;
    let (s, b) = parameter_identifier(s)?;
    Ok((
        s,
        PsParameterIdentifier::Scope(PsParameterIdentifierScope { nodes: (a, b) }),
    ))
}

pub fn ps_parameter_identifier_generate(s: Span) -> IResult<Span, PsParameterIdentifier> {
    let (s, a) = many0(triple(
        generate_block_identifier,
        opt(bracket(constant_expression)),
        symbol("."),
    ))(s)?;
    let (s, b) = parameter_identifier(s)?;
    Ok((
        s,
        PsParameterIdentifier::Generate(PsParameterIdentifierGenerate { nodes: (a, b) }),
    ))
}

pub fn ps_type_identifier(s: Span) -> IResult<Span, PsTypeIdentifier> {
    let (s, a) = opt(local_or_package_scope_or_class_scope)(s)?;
    let (s, b) = type_identifier(s)?;
    Ok((s, PsTypeIdentifier { nodes: (a, b) }))
}

pub fn sequence_identifier(s: Span) -> IResult<Span, SequenceIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, SequenceIdentifier { nodes: (a,) }))
}

pub fn signal_identifier(s: Span) -> IResult<Span, SignalIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, SignalIdentifier { nodes: (a,) }))
}

pub fn simple_identifier(s: Span) -> IResult<Span, SimpleIdentifier> {
    let (s, a) = ws(simple_identifier_impl)(s)?;
    Ok((s, SimpleIdentifier { nodes: a }))
}

pub fn simple_identifier_impl(s: Span) -> IResult<Span, Span> {
    let (s, a) = is_a(AZ_)(s)?;
    let (s, b) = opt(is_a(AZ09_DOLLAR))(s)?;
    let a = if let Some(b) = b {
        concat(a, b).unwrap()
    } else {
        a
    };
    Ok((s, a))
}

pub fn specparam_identifier(s: Span) -> IResult<Span, SpecparamIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, SpecparamIdentifier { nodes: (a,) }))
}

pub fn system_tf_identifier(s: Span) -> IResult<Span, SystemTfIdentifier> {
    let (s, a) = ws(system_tf_identifier_impl)(s)?;
    Ok((s, SystemTfIdentifier { nodes: a }))
}

pub fn system_tf_identifier_impl(s: Span) -> IResult<Span, Span> {
    let (s, a) = tag("$")(s)?;
    let (s, b) = is_a(AZ09_DOLLAR)(s)?;
    let a = concat(a, b).unwrap();
    Ok((s, a))
}

pub fn task_identifier(s: Span) -> IResult<Span, TaskIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TaskIdentifier { nodes: (a,) }))
}

pub fn tf_identifier(s: Span) -> IResult<Span, TfIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TfIdentifier { nodes: (a,) }))
}

pub fn terminal_identifier(s: Span) -> IResult<Span, TerminalIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TerminalIdentifier { nodes: (a,) }))
}

pub fn topmodule_identifier(s: Span) -> IResult<Span, TopmoduleIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TopmoduleIdentifier { nodes: (a,) }))
}

pub fn type_identifier(s: Span) -> IResult<Span, TypeIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TypeIdentifier { nodes: (a,) }))
}

pub fn udp_identifier(s: Span) -> IResult<Span, UdpIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, UdpIdentifier { nodes: (a,) }))
}

pub fn variable_identifier(s: Span) -> IResult<Span, VariableIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, VariableIdentifier { nodes: (a,) }))
}

pub fn implicit_class_handle_or_class_scope_or_package_scope(
    s: Span,
) -> IResult<Span, ImplicitClassHandleOrClassScopeOrPackageScope> {
    alt((
        map(pair(implicit_class_handle, symbol(".")), |x| {
            ImplicitClassHandleOrClassScopeOrPackageScope::ImplicitClassHandle(x)
        }),
        map(class_scope, |x| {
            ImplicitClassHandleOrClassScopeOrPackageScope::ClassScope(x)
        }),
        map(package_scope, |x| {
            ImplicitClassHandleOrClassScopeOrPackageScope::PackageScope(x)
        }),
    ))(s)
}

pub fn implicit_class_handle_or_package_scope(
    s: Span,
) -> IResult<Span, ImplicitClassHandleOrPackageScope> {
    alt((
        map(pair(implicit_class_handle, symbol(".")), |x| {
            ImplicitClassHandleOrPackageScope::ImplicitClassHandle(x)
        }),
        map(package_scope, |x| {
            ImplicitClassHandleOrPackageScope::PackageScope(x)
        }),
    ))(s)
}

pub fn implicit_class_handle_or_class_scope(
    s: Span,
) -> IResult<Span, ImplicitClassHandleOrClassScope> {
    alt((
        map(pair(implicit_class_handle, symbol(".")), |x| {
            ImplicitClassHandleOrClassScope::ImplicitClassHandle(x)
        }),
        map(class_scope, |x| {
            ImplicitClassHandleOrClassScope::ClassScope(x)
        }),
    ))(s)
}

pub fn package_scope_or_class_scope(s: Span) -> IResult<Span, PackageScopeOrClassScope> {
    alt((
        map(package_scope, |x| PackageScopeOrClassScope::PackageScope(x)),
        map(class_scope, |x| PackageScopeOrClassScope::ClassScope(x)),
    ))(s)
}

pub fn local_or_package_scope_or_class_scope(
    s: Span,
) -> IResult<Span, LocalOrPackageScopeOrClassScope> {
    alt((
        map(local, |x| LocalOrPackageScopeOrClassScope::Local(x)),
        map(package_scope, |x| {
            LocalOrPackageScopeOrClassScope::PackageScope(x)
        }),
        map(class_scope, |x| {
            LocalOrPackageScopeOrClassScope::ClassScope(x)
        }),
    ))(s)
}

pub fn local(s: Span) -> IResult<Span, Local> {
    let (s, a) = symbol("local")(s)?;
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
