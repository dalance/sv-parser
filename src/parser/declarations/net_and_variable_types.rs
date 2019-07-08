use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum CastingType<'a> {
    SimpleType(Box<SimpleType<'a>>),
    ConstantPrimary(Box<ConstantPrimary<'a>>),
    Signing(Box<Signing>),
    String,
    Const,
}

#[derive(Debug)]
pub enum DataType<'a> {
    Vector(DataTypeVector<'a>),
    Atom(DataTypeAtom),
    NonIntegerType(NonIntegerType),
    Union(DataTypeUnion<'a>),
    Enum(DataTypeEnum<'a>),
    String,
    Chandle,
    Virtual(DataTypeVirtual<'a>),
    Type(DataTypeType<'a>),
    ClassType(ClassType<'a>),
    Event,
    PsCovergroupIdentifier(PsCovergroupIdentifier<'a>),
    TypeReference(Box<TypeReference<'a>>),
}

#[derive(Debug)]
pub struct DataTypeVector<'a> {
    pub nodes: (IntegerVectorType, Option<Signing>, Vec<PackedDimension<'a>>),
}

#[derive(Debug)]
pub struct DataTypeAtom {
    pub nodes: (IntegerAtomType, Option<Signing>),
}

#[derive(Debug)]
pub struct DataTypeUnion<'a> {
    pub nodes: (
        StructUnion,
        Option<(Packed, Option<Signing>)>,
        Vec<StructUnionMember<'a>>,
    ),
}

#[derive(Debug)]
pub struct Packed {}

#[derive(Debug)]
pub struct DataTypeEnum<'a> {
    pub nodes: (
        Option<EnumBaseType<'a>>,
        Vec<EnumNameDeclaration<'a>>,
        Vec<PackedDimension<'a>>,
    ),
}

#[derive(Debug)]
pub struct DataTypeVirtual<'a> {
    pub nodes: (
        Option<Interface>,
        InterfaceIdentifier<'a>,
        Option<ParameterValueAssignment<'a>>,
        Option<ModportIdentifier<'a>>,
    ),
}

#[derive(Debug)]
pub struct Interface {}

#[derive(Debug)]
pub struct DataTypeType<'a> {
    pub nodes: (
        Option<PackageScopeOrClassScope<'a>>,
        TypeIdentifier<'a>,
        Vec<PackedDimension<'a>>,
    ),
}

#[derive(Debug)]
pub enum DataTypeOrImplicit<'a> {
    DataType(DataType<'a>),
    ImplicitDataType(ImplicitDataType<'a>),
}

#[derive(Debug)]
pub struct ImplicitDataType<'a> {
    pub nodes: (Option<Signing>, Vec<PackedDimension<'a>>),
}

#[derive(Debug)]
pub enum EnumBaseType<'a> {
    Atom(EnumBaseTypeAtom),
    Vector(EnumBaseTypeVector<'a>),
    Type(EnumBaseTypeType<'a>),
}

#[derive(Debug)]
pub struct EnumBaseTypeAtom {
    pub nodes: (IntegerAtomType, Option<Signing>),
}

#[derive(Debug)]
pub struct EnumBaseTypeVector<'a> {
    pub nodes: (
        IntegerVectorType,
        Option<Signing>,
        Option<PackedDimension<'a>>,
    ),
}

#[derive(Debug)]
pub struct EnumBaseTypeType<'a> {
    pub nodes: (Identifier<'a>, Option<PackedDimension<'a>>),
}

#[derive(Debug)]
pub struct EnumNameDeclaration<'a> {
    pub nodes: (
        Identifier<'a>,
        Option<(IntegralNumber<'a>, Option<IntegralNumber<'a>>)>,
        Option<ConstantExpression<'a>>,
    ),
}

#[derive(Debug)]
pub struct ClassScope<'a> {
    pub nodes: (ClassType<'a>,),
}

#[derive(Debug)]
pub struct ClassType<'a> {
    pub nodes: (
        Identifier<'a>,
        Option<ParameterValueAssignment<'a>>,
        Vec<(Identifier<'a>, Option<ParameterValueAssignment<'a>>)>,
    ),
}

#[derive(Debug)]
pub enum IntegerType {
    Vector(IntegerVectorType),
    Atom(IntegerAtomType),
}

#[derive(Debug)]
pub enum IntegerAtomType {
    Byte,
    Shortint,
    Int,
    Longint,
    Integer,
    Time,
}

#[derive(Debug)]
pub enum IntegerVectorType {
    Bit,
    Logic,
    Reg,
}

#[derive(Debug)]
pub enum NonIntegerType {
    Shortreal,
    Real,
    Realtime,
}

#[derive(Debug)]
pub enum NetType {
    Supply0,
    Supply1,
    Tri,
    Triand,
    Trior,
    Trireg,
    Tri0,
    Tri1,
    Uwire,
    Wire,
    Wand,
    Wor,
}

#[derive(Debug)]
pub enum NetPortType<'a> {
    DataType(NetPortTypeDataType<'a>),
    NetType(Identifier<'a>),
    Interconnect(ImplicitDataType<'a>),
}

#[derive(Debug)]
pub struct NetPortTypeDataType<'a> {
    pub nodes: (Option<NetType>, DataTypeOrImplicit<'a>),
}

#[derive(Debug)]
pub struct VariablePortType<'a> {
    pub nodes: (VarDataType<'a>,),
}

#[derive(Debug)]
pub enum VarDataType<'a> {
    DataType(DataType<'a>),
    DataTypeOrImplicit(DataTypeOrImplicit<'a>),
}

#[derive(Debug)]
pub enum Signing {
    Signed,
    Unsigned,
}

#[derive(Debug)]
pub enum SimpleType<'a> {
    IntegerType(IntegerType),
    NonNonIntegerType(IntegerType),
    TypeIdentifier(Identifier<'a>),
    ParameterIdentifier(Identifier<'a>),
}

#[derive(Debug)]
pub struct StructUnionMember<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Option<RandomQualifier>,
        DataTypeOrVoid<'a>,
        ListOfVariableDeclAssignments<'a>,
    ),
}

#[derive(Debug)]
pub enum DataTypeOrVoid<'a> {
    DataType(DataType<'a>),
    Void,
}

#[derive(Debug)]
pub enum StructUnion {
    Struct,
    Union,
    UnionTagged,
}

#[derive(Debug)]
pub enum TypeReference<'a> {
    Expression(Expression<'a>),
    DataType(DataType<'a>),
}

// -----------------------------------------------------------------------------

pub fn casting_type(s: &str) -> IResult<&str, CastingType> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn data_type(s: &str) -> IResult<&str, DataType> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn data_type_or_implicit(s: &str) -> IResult<&str, DataTypeOrImplicit> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn implicit_data_type(s: &str) -> IResult<&str, ImplicitDataType> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn enum_base_type(s: &str) -> IResult<&str, EnumBaseType> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn enum_name_declaration(s: &str) -> IResult<&str, EnumNameDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn class_scope(s: &str) -> IResult<&str, ClassScope> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn integer_type(s: &str) -> IResult<&str, IntegerType> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn integer_atom_type(s: &str) -> IResult<&str, IntegerAtomType> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn integer_vector_type(s: &str) -> IResult<&str, IntegerVectorType> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn non_integer_type(s: &str) -> IResult<&str, NonIntegerType> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn net_type(s: &str) -> IResult<&str, NetType> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn net_port_type(s: &str) -> IResult<&str, NetPortType> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn variable_port_type(s: &str) -> IResult<&str, VariablePortType> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn var_data_type(s: &str) -> IResult<&str, VarDataType> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn signing(s: &str) -> IResult<&str, Signing> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn simple_type(s: &str) -> IResult<&str, SimpleType> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn struct_union_member(s: &str) -> IResult<&str, StructUnionMember> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn data_type_or_void(s: &str) -> IResult<&str, DataTypeOrVoid> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn struct_union(s: &str) -> IResult<&str, StructUnion> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn type_reference(s: &str) -> IResult<&str, TypeReference> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}
