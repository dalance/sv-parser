use crate::parser::*;
use nom::branch::*;
use nom::bytes::complete::*;
use nom::combinator::*;
use nom::error::*;
use nom::sequence::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

const AZ_: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_";
const AZ09_: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_";
const AZ09_DOLLAR: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_$";

#[derive(Debug)]
pub struct ArrayIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct BlockIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct BinIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct CIdentifier<'a> {
    pub nodes: (&'a str,),
}

#[derive(Debug)]
pub struct CellIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct CheckerIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct ClassIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct ClassVariableIdentifier<'a> {
    pub nodes: (VariableIdentifier<'a>,),
}

#[derive(Debug)]
pub struct ClockingIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct ConfigIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct ConstIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct ConstraintIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct CovergroupIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct CovergroupVariableIdentifier<'a> {
    pub nodes: (VariableIdentifier<'a>,),
}

#[derive(Debug)]
pub struct CoverPointIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct CrossIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct DynamicArrayVariableIdentifier<'a> {
    pub nodes: (VariableIdentifier<'a>,),
}

#[derive(Debug)]
pub struct EnumIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct EscapedIdentifier<'a> {
    pub nodes: (&'a str,),
}

#[derive(Debug)]
pub struct FormalIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct FormalPortIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct FunctionIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct GenerateBlockIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
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
        Option<Root>,
        Vec<(Identifier<'a>, ConstantBitSelect<'a>)>,
        Identifier<'a>,
    ),
}

#[derive(Debug)]
pub struct Root {}

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

#[derive(Debug)]
pub enum Identifier<'a> {
    SimpleIdentifier(SimpleIdentifier<'a>),
    EscapedIdentifier(EscapedIdentifier<'a>),
}

#[derive(Debug)]
pub struct IndexVariableIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct InterfaceIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct InterfaceInstanceIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct InoutPortIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct InputPortIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct InstanceIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct LibraryIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct MemberIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct MethodIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct ModportIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct ModuleIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct NetIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct NetTypeIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct OutputPortIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct PackageIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub enum PackageScope<'a> {
    PackageIdentifier(PackageIdentifier<'a>),
    Unit,
}

#[derive(Debug)]
pub struct ParameterIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct PortIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct ProductionIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct ProgramIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct PropertyIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct PsClassIdentifier<'a> {
    pub nodes: (Option<PackageScope<'a>>, ClassIdentifier<'a>),
}

#[derive(Debug)]
pub struct PsCovergroupIdentifier<'a> {
    pub nodes: (Option<PackageScope<'a>>, CovergroupIdentifier<'a>),
}

#[derive(Debug)]
pub struct PsCheckerIdentifier<'a> {
    pub nodes: (Option<PackageScope<'a>>, CheckerIdentifier<'a>),
}

#[derive(Debug)]
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
    Hierarchical(PsOrHierarchicalNetIdentifierHierarchical<'a>),
}

#[derive(Debug)]
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
    Hierarchical(PsOrHierarchicalPropertyIdentifierHierarchical<'a>),
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
    Hierarchical(PsOrHierarchicalSequenceIdentifierHierarchical<'a>),
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
    Hierarchical(PsOrHierarchicalTfIdentifierHierarchical<'a>),
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
        Vec<(GenerateBlockIdentifier<'a>, Option<ConstantExpression<'a>>)>,
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
    Local,
    PackageScope(PackageScope<'a>),
    ClassScope(ClassScope<'a>),
}

#[derive(Debug)]
pub struct SequenceIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct SignalIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct SimpleIdentifier<'a> {
    pub nodes: (&'a str,),
}

#[derive(Debug)]
pub struct SpecparamIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct SystemTfIdentifier<'a> {
    pub nodes: (&'a str,),
}

#[derive(Debug)]
pub struct TaskIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct TfIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct TerminalIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct TopmoduleIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct TypeIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct UdpIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct VariableIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub enum ImplicitClassHandleOrClassScopeOrPackageScope<'a> {
    ImplicitClassHandle(ImplicitClassHandle),
    ClassScope(ClassScope<'a>),
    PackageScope(PackageScope<'a>),
}

#[derive(Debug)]
pub enum ImplicitClassHandleOrPackageScope<'a> {
    ImplicitClassHandle(ImplicitClassHandle),
    PackageScope(PackageScope<'a>),
}

#[derive(Debug)]
pub enum ImplicitClassHandleOrClassScope<'a> {
    ImplicitClassHandle(ImplicitClassHandle),
    ClassScope(ClassScope<'a>),
}

#[derive(Debug)]
pub enum PackageScopeOrClassScope<'a> {
    PackageScope(PackageScope<'a>),
    ClassScope(ClassScope<'a>),
}

// -----------------------------------------------------------------------------

pub fn array_identifier(s: &str) -> IResult<&str, ArrayIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ArrayIdentifier { nodes: (a,) }))
}

pub fn block_identifier(s: &str) -> IResult<&str, BlockIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, BlockIdentifier { nodes: (a,) }))
}

pub fn bin_identifier(s: &str) -> IResult<&str, BinIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, BinIdentifier { nodes: (a,) }))
}

pub fn c_identifier(s: &str) -> IResult<&str, CIdentifier> {
    ws(c_identifier_impl)(s)
}

pub fn c_identifier_impl(s: &str) -> IResult<&str, CIdentifier> {
    let (s, a) = is_a(AZ_)(s)?;
    let (s, b) = opt(is_a(AZ09_))(s)?;
    let a = if let Some(b) = b {
        str_concat::concat(a, b).unwrap()
    } else {
        a
    };
    Ok((s, CIdentifier { nodes: (a,) }))
}

pub fn cell_identifier(s: &str) -> IResult<&str, CellIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, CellIdentifier { nodes: (a,) }))
}

pub fn checker_identifier(s: &str) -> IResult<&str, CheckerIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, CheckerIdentifier { nodes: (a,) }))
}

pub fn class_identifier(s: &str) -> IResult<&str, ClassIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ClassIdentifier { nodes: (a,) }))
}

pub fn class_variable_identifier(s: &str) -> IResult<&str, ClassVariableIdentifier> {
    let (s, a) = variable_identifier(s)?;
    Ok((s, ClassVariableIdentifier { nodes: (a,) }))
}

pub fn clocking_identifier(s: &str) -> IResult<&str, ClockingIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ClockingIdentifier { nodes: (a,) }))
}

pub fn config_identifier(s: &str) -> IResult<&str, ConfigIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ConfigIdentifier { nodes: (a,) }))
}

pub fn const_identifier(s: &str) -> IResult<&str, ConstIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ConstIdentifier { nodes: (a,) }))
}

pub fn constraint_identifier(s: &str) -> IResult<&str, ConstraintIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ConstraintIdentifier { nodes: (a,) }))
}

pub fn covergroup_identifier(s: &str) -> IResult<&str, CovergroupIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, CovergroupIdentifier { nodes: (a,) }))
}

pub fn covergroup_variable_identifier(s: &str) -> IResult<&str, CovergroupVariableIdentifier> {
    let (s, a) = variable_identifier(s)?;
    Ok((s, CovergroupVariableIdentifier { nodes: (a,) }))
}

pub fn cover_point_identifier(s: &str) -> IResult<&str, CoverPointIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, CoverPointIdentifier { nodes: (a,) }))
}

pub fn cross_identifier(s: &str) -> IResult<&str, CrossIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, CrossIdentifier { nodes: (a,) }))
}

pub fn dynamic_array_variable_identifier(s: &str) -> IResult<&str, DynamicArrayVariableIdentifier> {
    let (s, a) = variable_identifier(s)?;
    Ok((s, DynamicArrayVariableIdentifier { nodes: (a,) }))
}

pub fn enum_identifier(s: &str) -> IResult<&str, EnumIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, EnumIdentifier { nodes: (a,) }))
}

pub fn escaped_identifier(s: &str) -> IResult<&str, EscapedIdentifier> {
    ws(escaped_identifier_impl)(s)
}

pub fn escaped_identifier_impl(s: &str) -> IResult<&str, EscapedIdentifier> {
    let (s, a) = tag("\\")(s)?;
    let (s, b) = is_not(" \t\r\n")(s)?;
    let a = str_concat::concat(a, b).unwrap();
    Ok((s, EscapedIdentifier { nodes: (a,) }))
}

pub fn formal_identifier(s: &str) -> IResult<&str, FormalIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, FormalIdentifier { nodes: (a,) }))
}

pub fn formal_port_identifier(s: &str) -> IResult<&str, FormalPortIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, FormalPortIdentifier { nodes: (a,) }))
}

pub fn function_identifier(s: &str) -> IResult<&str, FunctionIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, FunctionIdentifier { nodes: (a,) }))
}

pub fn generate_block_identifier(s: &str) -> IResult<&str, GenerateBlockIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, GenerateBlockIdentifier { nodes: (a,) }))
}

pub fn genvar_identifier(s: &str) -> IResult<&str, GenvarIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, GenvarIdentifier { nodes: (a,) }))
}

pub fn hierarchical_array_identifier(s: &str) -> IResult<&str, HierarchicalArrayIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalArrayIdentifier { nodes: (a,) }))
}

pub fn hierarchical_block_identifier(s: &str) -> IResult<&str, HierarchicalBlockIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalBlockIdentifier { nodes: (a,) }))
}

pub fn hierarchical_event_identifier(s: &str) -> IResult<&str, HierarchicalEventIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalEventIdentifier { nodes: (a,) }))
}

pub fn hierarchical_identifier(s: &str) -> IResult<&str, HierarchicalIdentifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn hierarchical_net_identifier(s: &str) -> IResult<&str, HierarchicalNetIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalNetIdentifier { nodes: (a,) }))
}

pub fn hierarchical_parameter_identifier(
    s: &str,
) -> IResult<&str, HierarchicalParameterIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalParameterIdentifier { nodes: (a,) }))
}

pub fn hierarchical_property_identifier(s: &str) -> IResult<&str, HierarchicalPropertyIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalPropertyIdentifier { nodes: (a,) }))
}

pub fn hierarchical_sequence_identifier(s: &str) -> IResult<&str, HierarchicalSequenceIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalSequenceIdentifier { nodes: (a,) }))
}

pub fn hierarchical_task_identifier(s: &str) -> IResult<&str, HierarchicalTaskIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalTaskIdentifier { nodes: (a,) }))
}

pub fn hierarchical_tf_identifier(s: &str) -> IResult<&str, HierarchicalTfIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalTfIdentifier { nodes: (a,) }))
}

pub fn hierarchical_variable_identifier(s: &str) -> IResult<&str, HierarchicalVariableIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalVariableIdentifier { nodes: (a,) }))
}

pub fn identifier(s: &str) -> IResult<&str, Identifier> {
    alt((
        map(escaped_identifier, |x| Identifier::EscapedIdentifier(x)),
        map(simple_identifier, |x| Identifier::SimpleIdentifier(x)),
    ))(s)
}

pub fn index_variable_identifier(s: &str) -> IResult<&str, IndexVariableIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, IndexVariableIdentifier { nodes: (a,) }))
}

pub fn interface_identifier(s: &str) -> IResult<&str, InterfaceIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, InterfaceIdentifier { nodes: (a,) }))
}

pub fn interface_instance_identifier(s: &str) -> IResult<&str, InterfaceInstanceIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, InterfaceInstanceIdentifier { nodes: (a,) }))
}

pub fn inout_port_identifier(s: &str) -> IResult<&str, InoutPortIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, InoutPortIdentifier { nodes: (a,) }))
}

pub fn input_port_identifier(s: &str) -> IResult<&str, InputPortIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, InputPortIdentifier { nodes: (a,) }))
}

pub fn instance_identifier(s: &str) -> IResult<&str, InstanceIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, InstanceIdentifier { nodes: (a,) }))
}

pub fn library_identifier(s: &str) -> IResult<&str, LibraryIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, LibraryIdentifier { nodes: (a,) }))
}

pub fn member_identifier(s: &str) -> IResult<&str, MemberIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, MemberIdentifier { nodes: (a,) }))
}

pub fn method_identifier(s: &str) -> IResult<&str, MethodIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, MethodIdentifier { nodes: (a,) }))
}

pub fn modport_identifier(s: &str) -> IResult<&str, ModportIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ModportIdentifier { nodes: (a,) }))
}

pub fn module_identifier(s: &str) -> IResult<&str, ModuleIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ModuleIdentifier { nodes: (a,) }))
}

pub fn net_identifier(s: &str) -> IResult<&str, NetIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, NetIdentifier { nodes: (a,) }))
}

pub fn net_type_identifier(s: &str) -> IResult<&str, NetTypeIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, NetTypeIdentifier { nodes: (a,) }))
}

pub fn output_port_identifier(s: &str) -> IResult<&str, OutputPortIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, OutputPortIdentifier { nodes: (a,) }))
}

pub fn package_identifier(s: &str) -> IResult<&str, PackageIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, PackageIdentifier { nodes: (a,) }))
}

pub fn package_scope(s: &str) -> IResult<&str, PackageScope> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn parameter_identifier(s: &str) -> IResult<&str, ParameterIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ParameterIdentifier { nodes: (a,) }))
}

pub fn port_identifier(s: &str) -> IResult<&str, PortIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, PortIdentifier { nodes: (a,) }))
}

pub fn production_identifier(s: &str) -> IResult<&str, ProductionIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ProductionIdentifier { nodes: (a,) }))
}

pub fn program_identifier(s: &str) -> IResult<&str, ProgramIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ProgramIdentifier { nodes: (a,) }))
}

pub fn property_identifier(s: &str) -> IResult<&str, PropertyIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, PropertyIdentifier { nodes: (a,) }))
}

pub fn ps_class_identifier(s: &str) -> IResult<&str, PsClassIdentifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn ps_covergroup_identifier(s: &str) -> IResult<&str, PsCovergroupIdentifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn ps_checker_identifier(s: &str) -> IResult<&str, PsCheckerIdentifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn ps_identifier(s: &str) -> IResult<&str, PsIdentifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn ps_or_hierarchical_array_identifier(
    s: &str,
) -> IResult<&str, PsOrHierarchicalArrayIdentifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn ps_or_hierarchical_net_identifier(s: &str) -> IResult<&str, PsOrHierarchicalNetIdentifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn ps_or_hierarchical_property_identifier(
    s: &str,
) -> IResult<&str, PsOrHierarchicalPropertyIdentifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn ps_or_hierarchical_sequence_identifier(
    s: &str,
) -> IResult<&str, PsOrHierarchicalSequenceIdentifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn ps_or_hierarchical_tf_identifier(s: &str) -> IResult<&str, PsOrHierarchicalTfIdentifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn ps_parameter_identifier(s: &str) -> IResult<&str, PsParameterIdentifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn ps_type_identifier(s: &str) -> IResult<&str, PsTypeIdentifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_identifier(s: &str) -> IResult<&str, SequenceIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, SequenceIdentifier { nodes: (a,) }))
}

pub fn signal_identifier(s: &str) -> IResult<&str, SignalIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, SignalIdentifier { nodes: (a,) }))
}

pub fn simple_identifier(s: &str) -> IResult<&str, SimpleIdentifier> {
    ws(simple_identifier_impl)(s)
}

pub fn simple_identifier_impl(s: &str) -> IResult<&str, SimpleIdentifier> {
    let (s, a) = is_a(AZ_)(s)?;
    let (s, b) = opt(is_a(AZ09_DOLLAR))(s)?;
    let a = if let Some(b) = b {
        str_concat::concat(a, b).unwrap()
    } else {
        a
    };
    Ok((s, SimpleIdentifier { nodes: (a,) }))
}

pub fn specparam_identifier(s: &str) -> IResult<&str, SpecparamIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, SpecparamIdentifier { nodes: (a,) }))
}

pub fn system_tf_identifier(s: &str) -> IResult<&str, SystemTfIdentifier> {
    ws(system_tf_identifier_impl)(s)
}

pub fn system_tf_identifier_impl(s: &str) -> IResult<&str, SystemTfIdentifier> {
    let (s, a) = tag("$")(s)?;
    let (s, b) = is_a(AZ09_DOLLAR)(s)?;
    let a = str_concat::concat(a, b).unwrap();
    Ok((s, SystemTfIdentifier { nodes: (a,) }))
}

pub fn task_identifier(s: &str) -> IResult<&str, TaskIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TaskIdentifier { nodes: (a,) }))
}

pub fn tf_identifier(s: &str) -> IResult<&str, TfIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TfIdentifier { nodes: (a,) }))
}

pub fn terminal_identifier(s: &str) -> IResult<&str, TerminalIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TerminalIdentifier { nodes: (a,) }))
}

pub fn topmodule_identifier(s: &str) -> IResult<&str, TopmoduleIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TopmoduleIdentifier { nodes: (a,) }))
}

pub fn type_identifier(s: &str) -> IResult<&str, TypeIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TypeIdentifier { nodes: (a,) }))
}

pub fn udp_identifier(s: &str) -> IResult<&str, UdpIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, UdpIdentifier { nodes: (a,) }))
}

pub fn variable_identifier(s: &str) -> IResult<&str, VariableIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, VariableIdentifier { nodes: (a,) }))
}

pub fn implicit_class_handle_or_class_scope_or_package_scope(
    s: &str,
) -> IResult<&str, ImplicitClassHandleOrClassScopeOrPackageScope> {
    alt((
        map(terminated(implicit_class_handle, symbol(".")), |x| {
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
    s: &str,
) -> IResult<&str, ImplicitClassHandleOrPackageScope> {
    alt((
        map(terminated(implicit_class_handle, symbol(".")), |x| {
            ImplicitClassHandleOrPackageScope::ImplicitClassHandle(x)
        }),
        map(package_scope, |x| {
            ImplicitClassHandleOrPackageScope::PackageScope(x)
        }),
    ))(s)
}

pub fn implicit_class_handle_or_class_scope(
    s: &str,
) -> IResult<&str, ImplicitClassHandleOrClassScope> {
    alt((
        map(terminated(implicit_class_handle, symbol(".")), |x| {
            ImplicitClassHandleOrClassScope::ImplicitClassHandle(x)
        }),
        map(class_scope, |x| {
            ImplicitClassHandleOrClassScope::ClassScope(x)
        }),
    ))(s)
}

pub fn package_scope_or_class_scope(s: &str) -> IResult<&str, PackageScopeOrClassScope> {
    alt((
        map(package_scope, |x| PackageScopeOrClassScope::PackageScope(x)),
        map(class_scope, |x| PackageScopeOrClassScope::ClassScope(x)),
    ))(s)
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        assert_eq!(
            format!("{:?}", all_consuming(identifier)("shiftreg_a")),
            "Ok((\"\", Identifier { raw: \"shiftreg_a\" }))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(identifier)("_bus3")),
            "Ok((\"\", Identifier { raw: \"_bus3\" }))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(identifier)("n$657")),
            "Ok((\"\", Identifier { raw: \"n$657\" }))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(identifier)("\\busa+index")),
            "Ok((\"\", Identifier { raw: \"\\\\busa+index\" }))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(identifier)("\\-clock")),
            "Ok((\"\", Identifier { raw: \"\\\\-clock\" }))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(system_tf_identifier)("$display")),
            "Ok((\"\", Identifier { raw: \"$display\" }))"
        );
    }
}
