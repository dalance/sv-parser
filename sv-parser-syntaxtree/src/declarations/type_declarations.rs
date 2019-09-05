use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub enum DataDeclaration {
    Variable(Box<DataDeclarationVariable>),
    TypeDeclaration(Box<TypeDeclaration>),
    PackageImportDeclaration(Box<PackageImportDeclaration>),
    NetTypeDeclaration(Box<NetTypeDeclaration>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct DataDeclarationVariable {
    pub nodes: (
        Option<Const>,
        Option<Var>,
        Option<Lifetime>,
        DataTypeOrImplicit,
        ListOfVariableDeclAssignments,
        Symbol,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct Const {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PackageImportDeclaration {
    pub nodes: (Keyword, List<Symbol, PackageImportItem>, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum PackageImportItem {
    Identifier(Box<PackageImportItemIdentifier>),
    Asterisk(Box<PackageImportItemAsterisk>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PackageImportItemIdentifier {
    pub nodes: (PackageIdentifier, Symbol, Identifier),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PackageImportItemAsterisk {
    pub nodes: (PackageIdentifier, Symbol, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum PackageExportDeclaration {
    Asterisk(Box<PackageExportDeclarationAsterisk>),
    Item(Box<PackageExportDeclarationItem>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PackageExportDeclarationAsterisk {
    pub nodes: (Keyword, Symbol, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PackageExportDeclarationItem {
    pub nodes: (Keyword, List<Symbol, PackageImportItem>, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct GenvarDeclaration {
    pub nodes: (Keyword, ListOfGenvarIdentifiers, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum NetDeclaration {
    NetType(Box<NetDeclarationNetType>),
    NetTypeIdentifier(Box<NetDeclarationNetTypeIdentifier>),
    Interconnect(Box<NetDeclarationInterconnect>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct NetDeclarationNetType {
    pub nodes: (
        NetType,
        Option<Strength>,
        Option<VectorScalar>,
        DataTypeOrImplicit,
        Option<Delay3>,
        ListOfNetDeclAssignments,
        Symbol,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum Strength {
    Drive(Box<DriveStrength>),
    Charge(Box<ChargeStrength>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum VectorScalar {
    Vectored(Box<Keyword>),
    Scalared(Box<Keyword>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct NetDeclarationNetTypeIdentifier {
    pub nodes: (
        NetTypeIdentifier,
        Option<DelayControl>,
        ListOfNetDeclAssignments,
        Symbol,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct NetDeclarationInterconnect {
    pub nodes: (
        Keyword,
        ImplicitDataType,
        Option<(Symbol, DelayValue)>,
        NetIdentifier,
        Vec<UnpackedDimension>,
        Option<(Symbol, NetIdentifier, Vec<UnpackedDimension>)>,
        Symbol,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum TypeDeclaration {
    DataType(Box<TypeDeclarationDataType>),
    Interface(Box<TypeDeclarationInterface>),
    Reserved(Box<TypeDeclarationReserved>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TypeDeclarationDataType {
    pub nodes: (
        Keyword,
        DataType,
        TypeIdentifier,
        Vec<VariableDimension>,
        Symbol,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TypeDeclarationInterface {
    pub nodes: (
        Keyword,
        InterfaceInstanceIdentifier,
        ConstantBitSelect,
        Symbol,
        TypeIdentifier,
        TypeIdentifier,
        Symbol,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TypeDeclarationReserved {
    pub nodes: (
        Keyword,
        Option<TypeDeclarationKeyword>,
        TypeIdentifier,
        Symbol,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum TypeDeclarationKeyword {
    Enum(Box<Keyword>),
    Struct(Box<Keyword>),
    Union(Box<Keyword>),
    Class(Box<Keyword>),
    InterfaceClass(Box<(Keyword, Keyword)>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum NetTypeDeclaration {
    DataType(Box<NetTypeDeclarationDataType>),
    NetType(Box<NetTypeDeclarationNetType>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct NetTypeDeclarationDataType {
    pub nodes: (
        Keyword,
        DataType,
        NetTypeIdentifier,
        Option<(Keyword, Option<PackageScopeOrClassScope>, TfIdentifier)>,
        Symbol,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct NetTypeDeclarationNetType {
    pub nodes: (
        Keyword,
        Option<PackageScopeOrClassScope>,
        NetTypeIdentifier,
        NetTypeIdentifier,
        Symbol,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum Lifetime {
    Static(Box<Keyword>),
    Automatic(Box<Keyword>),
}
