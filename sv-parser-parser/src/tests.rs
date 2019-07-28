#![cfg(test)]

use crate::*;

macro_rules! test {
    ( $x:expr, $y:expr, $z:pat ) => {
        #[cfg(not(feature = "trace"))]
        let info = SpanInfo::default();
        #[cfg(feature = "trace")]
        let info = {
            let mut info = SpanInfo::default();
            info.tracable_info = TracableInfo::new().forward(true).backward(true);
            info
        };
        let ret = all_consuming($x)(Span::new_extra($y, info));
        if let $z = ret {
        } else {
            assert!(false, "{:?}", ret)
        }
    };
}

#[test]
fn test_pulldown_strength() {
    test!(pulldown_strength, "(supply0, strong1)", Ok((_, _)));
    test!(pulldown_strength, "(pull1, weak0)", Ok((_, _)));
    test!(pulldown_strength, "(pull0)", Ok((_, _)));
    test!(pulldown_strength, "(pull0)", Ok((_, _)));
    test!(pulldown_strength, "(pull0)", Ok((_, _)));
}

#[test]
fn test_pullup_strength() {
    test!(pullup_strength, "(supply0, strong1)", Ok((_, _)));
    test!(pullup_strength, "(pull1, weak0)", Ok((_, _)));
    test!(pullup_strength, "(supply1)", Ok((_, _)));
}

#[test]
fn test_cmos_switchtype() {
    test!(cmos_switchtype, "cmos ", Ok((_, _)));
    test!(cmos_switchtype, "rcmos ", Ok((_, _)));
}

#[test]
fn test_enable_gatetype() {
    test!(enable_gatetype, "bufif0 ", Ok((_, _)));
    test!(enable_gatetype, "bufif1 ", Ok((_, _)));
    test!(enable_gatetype, "notif0 ", Ok((_, _)));
    test!(enable_gatetype, "notif1 ", Ok((_, _)));
}

#[test]
fn test_mos_switchtype() {
    test!(mos_switchtype, "nmos ", Ok((_, _)));
    test!(mos_switchtype, "pmos ", Ok((_, _)));
    test!(mos_switchtype, "rnmos ", Ok((_, _)));
    test!(mos_switchtype, "rpmos ", Ok((_, _)));
}

#[test]
fn test_n_input_gatetype() {
    test!(n_input_gatetype, "and ", Ok((_, _)));
    test!(n_input_gatetype, "nand ", Ok((_, _)));
    test!(n_input_gatetype, "or ", Ok((_, _)));
    test!(n_input_gatetype, "nor ", Ok((_, _)));
    test!(n_input_gatetype, "xor ", Ok((_, _)));
    test!(n_input_gatetype, "xnor ", Ok((_, _)));
}

#[test]
fn test_n_output_gatetype() {
    test!(n_output_gatetype, "buf ", Ok((_, _)));
    test!(n_output_gatetype, "not ", Ok((_, _)));
}

#[test]
fn test_pass_en_switchtype() {
    test!(pass_en_switchtype, "tranif0 ", Ok((_, _)));
    test!(pass_en_switchtype, "tranif1 ", Ok((_, _)));
    test!(pass_en_switchtype, "rtranif0 ", Ok((_, _)));
    test!(pass_en_switchtype, "rtranif1 ", Ok((_, _)));
}

#[test]
fn test_pass_switchtype() {
    test!(pass_switchtype, "tran ", Ok((_, _)));
    test!(pass_switchtype, "rtran ", Ok((_, _)));
}

#[test]
fn test_library_text() {
    test!(
        library_text,
        "library rtlLib \"*.v\" -incdir \"aaa\";\ninclude \"bbb\";;",
        Ok((_, _))
    );
}

#[test]
fn test_timeunits_declaration() {
    test!(timeunits_declaration, "timeunit 1.0ps;", Ok((_, _)));
    test!(timeunits_declaration, "timeunit 1.0ps / 20ms;", Ok((_, _)));
    test!(timeunits_declaration, "timeprecision 10.0fs;", Ok((_, _)));
    test!(
        timeunits_declaration,
        "timeunit 10.0fs; timeprecision 20s;",
        Ok((_, _))
    );
    test!(
        timeunits_declaration,
        "timeprecision 10.0fs; timeunit 20s \n;",
        Ok((_, _))
    );
}

#[test]
fn test_data_type() {
    test!(
        data_type,
        "struct { bit [7:0] opcode; bit [23:0] addr; }",
        Ok((_, DataType::StructUnion(_)))
    );
    test!(
        data_type,
        "struct packed signed { int a; shortint b; byte c; bit [7:0] d; }",
        Ok((_, DataType::StructUnion(_)))
    );
    test!(
        data_type,
        "union { int i; shortreal f; } ",
        Ok((_, DataType::StructUnion(_)))
    );
    test!(
        data_type,
        "struct { bit isfloat; union { int i; shortreal f; } n; }",
        Ok((_, DataType::StructUnion(_)))
    );
    test!(
        data_type,
        "union packed { s_atmcell acell; bit [423:0] bit_slice; bit [52:0][7:0] byte_slice; }",
        Ok((_, DataType::StructUnion(_)))
    );
    test!(
        data_type,
        "union tagged { void Invalid; int Valid; }",
        Ok((_, DataType::StructUnion(_)))
    );
}

#[test]
fn test_local_parameter_declaration() {
    test!(
        local_parameter_declaration,
        "localparam byte colon1 = \":\" ",
        Ok((_, LocalParameterDeclaration::Param(_)))
    );
}

#[test]
fn test_parameter_declaration() {
    test!(
        parameter_declaration,
        "parameter logic flag = 1 ",
        Ok((_, ParameterDeclaration::Param(_)))
    );
    test!(
        parameter_declaration,
        "parameter e = 25, f = 9 ",
        Ok((_, ParameterDeclaration::Param(_)))
    );
    test!(
        parameter_declaration,
        "parameter byte_size = 8, byte_mask = byte_size - 1",
        Ok((_, ParameterDeclaration::Param(_)))
    );
    test!(
        parameter_declaration,
        "parameter signed [3:0] mux_selector = 0",
        Ok((_, ParameterDeclaration::Param(_)))
    );
    test!(
        parameter_declaration,
        "parameter real r1 = 3.5e17",
        Ok((_, ParameterDeclaration::Param(_)))
    );
    test!(
        parameter_declaration,
        "parameter logic [31:0] P1 [3:0] = '{ 1, 2, 3, 4 } ",
        Ok((_, ParameterDeclaration::Param(_)))
    );
    test!(
        parameter_declaration,
        "parameter r2 = $ ",
        Ok((_, ParameterDeclaration::Param(_)))
    );
    test!(
        parameter_declaration,
        "parameter type p2 = shortint ",
        Ok((_, ParameterDeclaration::Type(_)))
    );
}

#[test]
fn test_specparam_declaration() {
    test!(specparam_declaration, "specparam delay = 10 ; ", Ok((_, _)));
    test!(
        specparam_declaration,
        "specparam tRise_clk_q = 150, tFall_clk_q = 200;",
        Ok((_, _))
    );
}

#[test]
fn test_inout_declaration() {
    test!(inout_declaration, "inout a", Ok((_, _)));
    test!(inout_declaration, "inout [7:0] a", Ok((_, _)));
    test!(inout_declaration, "inout signed [7:0] a", Ok((_, _)));
}

#[test]
fn test_net_type_declaration() {
    test!(
        net_type_declaration,
        "nettype T wT;",
        Ok((_, NetTypeDeclaration::DataType(_)))
    );
    test!(
        net_type_declaration,
        "nettype T wTsum with Tsum;",
        Ok((_, NetTypeDeclaration::DataType(_)))
    );
    test!(
        net_type_declaration,
        "nettype MyBaseT::T narrowTsum with MyBaseT::Tsum;",
        Ok((_, NetTypeDeclaration::DataType(_)))
    );
}

#[test]
fn test_net_declaration() {
    test!(
        net_declaration,
        "trireg (large) logic #(0,0,0) cap1;",
        Ok((_, NetDeclaration::NetType(_)))
    );
    test!(
        net_declaration,
        "wire addressT w1;",
        Ok((_, NetDeclaration::NetType(_)))
    );
    test!(
        net_declaration,
        "wire struct packed { logic ecc; logic [7:0] data; } memsig;",
        Ok((_, NetDeclaration::NetType(_)))
    );
    test!(
        net_declaration,
        "wire w;",
        Ok((_, NetDeclaration::NetType(_)))
    );
    test!(
        net_declaration,
        "wire [15:0] w;",
        Ok((_, NetDeclaration::NetType(_)))
    );
    test!(
        net_declaration,
        "interconnect w1;",
        Ok((_, NetDeclaration::Interconnect(_)))
    );
    test!(
        net_declaration,
        "interconnect [3:0] w2;",
        Ok((_, NetDeclaration::Interconnect(_)))
    );
    test!(
        net_declaration,
        "interconnect [3:0] w3 [1:0];",
        Ok((_, NetDeclaration::Interconnect(_)))
    );
    test!(net_declaration, "interconnect logic [3:0] w4;", Err(_));
    test!(net_declaration, "interconnect #(1,2,3) w5;", Err(_));
    test!(
        net_declaration,
        "wand w;",
        Ok((_, NetDeclaration::NetType(_)))
    );
    test!(
        net_declaration,
        "tri [15:0] busa;",
        Ok((_, NetDeclaration::NetType(_)))
    );
    test!(
        net_declaration,
        "trireg (small) storeit;",
        Ok((_, NetDeclaration::NetType(_)))
    );
    test!(
        net_declaration,
        "wire w1, w2;",
        Ok((_, NetDeclaration::NetType(_)))
    );
    test!(
        net_declaration,
        "tri1 scalared [63:0] bus64;",
        Ok((_, NetDeclaration::NetType(_)))
    );
    test!(
        net_declaration,
        "tri vectored [31:0] data;",
        Ok((_, NetDeclaration::NetType(_)))
    );
}

#[test]
fn test_data_declaration() {
    //test!(
    //    data_declaration,
    //    "shortint s1, s2[0:9];",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "var byte my_byte;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "var v;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "var [15:0] vw;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "var enum bit { clear, error } status;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "var reg r;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "int i = 0;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "logic a;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "logic[3:0] v;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "logic signed [3:0] signed_reg;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "logic [-1:4] b;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "logic [4:0] x, y, z;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "int unsigned ui;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "int signed si;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "string myName = default_name;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "byte c = \"A\";",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "bit [10:0] b = \"x41\";",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "bit [1:4][7:0] h = \"hello\" ;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "event done;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "event done_too = done;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "event empty = null;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "typedef int intP;",
    //    Ok((_, DataDeclaration::TypeDeclaration(_)))
    //);
    //test!(
    //    data_declaration,
    //    "intP a, b;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "typedef enum type_identifier;",
    //    Ok((_, DataDeclaration::TypeDeclaration(_)))
    //);
    //test!(
    //    data_declaration,
    //    "typedef struct type_identifier;",
    //    Ok((_, DataDeclaration::TypeDeclaration(_)))
    //);
    //test!(
    //    data_declaration,
    //    "typedef union type_identifier;",
    //    Ok((_, DataDeclaration::TypeDeclaration(_)))
    //);
    //test!(
    //    data_declaration,
    //    "typedef class type_identifier;",
    //    Ok((_, DataDeclaration::TypeDeclaration(_)))
    //);
    //test!(
    //    data_declaration,
    //    "typedef interface class type_identifier;",
    //    Ok((_, DataDeclaration::TypeDeclaration(_)))
    //);
    //test!(
    //    data_declaration,
    //    "typedef type_identifier;",
    //    Ok((_, DataDeclaration::TypeDeclaration(_)))
    //);
    //test!(
    //    data_declaration,
    //    "typedef C::T c_t;",
    //    Ok((_, DataDeclaration::TypeDeclaration(_)))
    //);
    //test!(
    //    data_declaration,
    //    "enum {red, yellow, green} light1, light2;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "enum bit [1:0] {IDLE, XX='x, S1=2'b01, S2=2'b10} state, next;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "enum integer {IDLE, XX='x, S1='b01, S2='b10} state, next;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "enum integer {IDLE, XX='x, S1='b01, S2='b10} state, next;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "enum {bronze=3, silver, gold} medal;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "enum {a=3, b=7, c} alphabet;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "enum bit [3:0] {bronze='h3, silver, gold='h5} medal2;",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "integer i_array[*];",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "bit [20:0] array_b[string];",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "event ev_array[myClass];",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "int array_name [*];",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "int array_name1 [ integer ];",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "int a[int] = '{default:1};",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    //test!(
    //    data_declaration,
    //    "byte q1[$];",
    //    Ok((_, DataDeclaration::Variable(_)))
    //);
    test!(primary, "'{default:1}", Ok((_, _)));
}

#[test]
fn test_drive_strength() {
    test!(drive_strength, "(supply0, strong1)", Ok((_, _)));
    test!(drive_strength, "(pull1, weak0)", Ok((_, _)));
    test!(drive_strength, "(pull0, highz1)", Ok((_, _)));
    test!(drive_strength, "(weak1, highz0)", Ok((_, _)));
    test!(drive_strength, "(highz0, supply1)", Ok((_, _)));
    test!(drive_strength, "(highz1, strong0)", Ok((_, _)));
}

#[test]
fn test_charge_strength() {
    test!(charge_strength, "( small)", Ok((_, _)));
    test!(charge_strength, "( medium  )", Ok((_, _)));
    test!(charge_strength, "(large)", Ok((_, _)));
}

#[test]
fn test_blocking_assignment() {
    test!(
        blocking_assignment,
        "idest = new [3] (isrc)",
        Ok((_, BlockingAssignment::NonrangeVariable(_)))
    );
}

#[test]
fn test_primary() {
    test!(primary, "2.1ns ", Ok((_, Primary::PrimaryLiteral(_))));
    test!(primary, "40 ps ", Ok((_, Primary::PrimaryLiteral(_))));
    test!(primary, "'0", Ok((_, Primary::PrimaryLiteral(_))));
    test!(primary, "10", Ok((_, Primary::PrimaryLiteral(_))));
    test!(primary, "\"aaa\"", Ok((_, Primary::PrimaryLiteral(_))));
    test!(primary, "this ", Ok((_, Primary::This(_))));
    test!(primary, "$", Ok((_, Primary::Dollar(_))));
    test!(primary, "null ", Ok((_, Primary::Null(_))));
}

#[test]
fn test_cast() {
    test!(cast, "int'(2.0 * 3.0)", Ok((_, _)));
    test!(cast, "shortint'({8'hFA,8'hCE}) ", Ok((_, _)));
    test!(cast, "signed'(x)", Ok((_, _)));
    test!(cast, "const'(x)", Ok((_, _)));
    test!(cast, "type_t'(x)", Ok((_, _)));
}

#[test]
fn test_number() {
    test!(number, "659", Ok((_, Number::IntegralNumber(_))));
    test!(number, "'h 837FF", Ok((_, Number::IntegralNumber(_))));
    test!(number, "'h 837FF", Ok((_, Number::IntegralNumber(_))));
    test!(number, "'o7460", Ok((_, Number::IntegralNumber(_))));
    test!(number, "'4af", Err(_));
    test!(number, "4'b1001", Ok((_, Number::IntegralNumber(_))));
    test!(number, "5 'D 3", Ok((_, Number::IntegralNumber(_))));
    test!(number, "3'b01x", Ok((_, Number::IntegralNumber(_))));
    test!(number, "12'hx", Ok((_, Number::IntegralNumber(_))));
    test!(number, "16'hz", Ok((_, Number::IntegralNumber(_))));
    test!(number, "8 'd -6", Err(_));
    test!(number, "4 'shf", Ok((_, Number::IntegralNumber(_))));
    test!(number, "16'sd?", Ok((_, Number::IntegralNumber(_))));
    test!(number, "27_195_000", Ok((_, Number::IntegralNumber(_))));
    test!(
        number,
        "16'b0011_0101_0001_1111",
        Ok((_, Number::IntegralNumber(_)))
    );
    test!(
        number,
        "32 'h 12ab_f001",
        Ok((_, Number::IntegralNumber(_)))
    );
    test!(number, "1.2", Ok((_, Number::RealNumber(_))));
    test!(number, "0.1", Ok((_, Number::RealNumber(_))));
    test!(number, "2394.26331", Ok((_, Number::RealNumber(_))));
    test!(number, "1.2E12", Ok((_, Number::RealNumber(_))));
    test!(number, "1.30e-2", Ok((_, Number::RealNumber(_))));
    test!(number, "0.1e-0", Ok((_, Number::RealNumber(_))));
    test!(number, "23E10", Ok((_, Number::RealNumber(_))));
    test!(number, "29E-2", Ok((_, Number::RealNumber(_))));
    test!(number, "236.123_763_e-12", Ok((_, Number::RealNumber(_))));
    test!(number, ".12", Err(_));
    test!(number, "9.", Err(_));
    test!(number, "4.E3", Err(_));
    test!(number, ".2e-7", Err(_));
}

#[test]
fn test_unbased_unsized_literal() {
    test!(unbased_unsized_literal, "'0", Ok((_, _)));
    test!(unbased_unsized_literal, "'1", Ok((_, _)));
    test!(unbased_unsized_literal, "'x", Ok((_, _)));
    test!(unbased_unsized_literal, "'z", Ok((_, _)));
}

#[test]
fn test_net_lvalue() {
    test!(net_lvalue, "A", Ok((_, _)));
    test!(net_lvalue, "{A[7:0],A[15:8],A[23:16]}", Ok((_, _)));
    test!(net_lvalue, "'{A[7:0],A[15:8]}", Ok((_, _)));
}

#[test]
fn test_variable_lvalue() {
    test!(variable_lvalue, "A", Ok((_, _)));
    test!(variable_lvalue, "{A[7:0],A[15:8],A[23:16]}", Ok((_, _)));
    test!(variable_lvalue, "'{A[7:0],A[15:8]}", Ok((_, _)));
}

#[test]
fn test_nonrange_variable_lvalue() {
    test!(nonrange_variable_lvalue, "A", Ok((_, _)));
    test!(nonrange_variable_lvalue, "A[1][2][3]", Ok((_, _)));
    //TODO
    //test!(nonrange_variable_lvalue, "A[][2][3]", Ok((_, _)));
    //test!(nonrange_variable_lvalue, "A[][]", Ok((_, _)));
}

#[test]
fn test_unary_operator() {
    test!(unary_operator, "+", Ok((_, _)));
    test!(unary_operator, "-", Ok((_, _)));
    test!(unary_operator, "!", Ok((_, _)));
    test!(unary_operator, "&", Ok((_, _)));
    test!(unary_operator, "|", Ok((_, _)));
    test!(unary_operator, "~&", Ok((_, _)));
    test!(unary_operator, "~|", Ok((_, _)));
    test!(unary_operator, "~^", Ok((_, _)));
    test!(unary_operator, "^~", Ok((_, _)));
    test!(unary_operator, "^", Ok((_, _)));
    test!(unary_operator, "~", Ok((_, _)));
}

#[test]
fn test_binary_operator() {
    test!(binary_operator, "+", Ok((_, _)));
    test!(binary_operator, "-", Ok((_, _)));
    test!(binary_operator, "**", Ok((_, _)));
    test!(binary_operator, "*", Ok((_, _)));
    test!(binary_operator, "/", Ok((_, _)));
    test!(binary_operator, "%", Ok((_, _)));
    test!(binary_operator, "===", Ok((_, _)));
    test!(binary_operator, "==?", Ok((_, _)));
    test!(binary_operator, "==", Ok((_, _)));
    test!(binary_operator, "!==", Ok((_, _)));
    test!(binary_operator, "!=?", Ok((_, _)));
    test!(binary_operator, "!=", Ok((_, _)));
    test!(binary_operator, "&&", Ok((_, _)));
    test!(binary_operator, "||", Ok((_, _)));
    test!(binary_operator, "&", Ok((_, _)));
    test!(binary_operator, "|", Ok((_, _)));
    test!(binary_operator, "^~", Ok((_, _)));
    test!(binary_operator, "^", Ok((_, _)));
    test!(binary_operator, "~^", Ok((_, _)));
    test!(binary_operator, ">>>", Ok((_, _)));
    test!(binary_operator, ">>", Ok((_, _)));
    test!(binary_operator, "<<<", Ok((_, _)));
    test!(binary_operator, "<<", Ok((_, _)));
    test!(binary_operator, "->", Ok((_, _)));
    test!(binary_operator, "<->", Ok((_, _)));
    test!(binary_operator, "<=", Ok((_, _)));
    test!(binary_operator, "<", Ok((_, _)));
    test!(binary_operator, ">=", Ok((_, _)));
    test!(binary_operator, ">", Ok((_, _)));
}

#[test]
fn test_inc_or_dec_operator() {
    test!(inc_or_dec_operator, "++", Ok((_, _)));
    test!(inc_or_dec_operator, "--", Ok((_, _)));
}

#[test]
fn test_unary_module_path_operator() {
    test!(unary_module_path_operator, "!", Ok((_, _)));
    test!(unary_module_path_operator, "&", Ok((_, _)));
    test!(unary_module_path_operator, "|", Ok((_, _)));
    test!(unary_module_path_operator, "~&", Ok((_, _)));
    test!(unary_module_path_operator, "~|", Ok((_, _)));
    test!(unary_module_path_operator, "~^", Ok((_, _)));
    test!(unary_module_path_operator, "^~", Ok((_, _)));
    test!(unary_module_path_operator, "^", Ok((_, _)));
    test!(unary_module_path_operator, "~", Ok((_, _)));
}

#[test]
fn test_binary_module_path_operator() {
    test!(binary_module_path_operator, "==", Ok((_, _)));
    test!(binary_module_path_operator, "!=", Ok((_, _)));
    test!(binary_module_path_operator, "&&", Ok((_, _)));
    test!(binary_module_path_operator, "||", Ok((_, _)));
    test!(binary_module_path_operator, "&", Ok((_, _)));
    test!(binary_module_path_operator, "|", Ok((_, _)));
    test!(binary_module_path_operator, "^~", Ok((_, _)));
    test!(binary_module_path_operator, "^", Ok((_, _)));
    test!(binary_module_path_operator, "~^", Ok((_, _)));
}

#[test]
fn test_string_literal() {
    test!(string_literal, "\"aaa aaaa\"", Ok((_, _)));
    test!(string_literal, r#""aaa\" aaaa""#, Ok((_, _)));
    test!(string_literal, r#""aaa\"""#, Ok((_, _)));
}

#[test]
fn test_identifier() {
    test!(
        identifier,
        "shiftreg_a",
        Ok((_, Identifier::SimpleIdentifier(_)))
    );
    test!(
        identifier,
        "_bus3",
        Ok((_, Identifier::SimpleIdentifier(_)))
    );
    test!(
        identifier,
        "n$657",
        Ok((_, Identifier::SimpleIdentifier(_)))
    );
    test!(
        identifier,
        "\\busa+index",
        Ok((_, Identifier::EscapedIdentifier(_)))
    );
    test!(
        identifier,
        "\\-clock",
        Ok((_, Identifier::EscapedIdentifier(_)))
    );
}

#[test]
fn test_system_tf_identifier() {
    test!(system_tf_identifier, "$display", Ok((_, _)));
}

#[test]
fn test_comment() {
    test!(comment, "// comment", Ok((_, _)));
    test!(comment, "/* comment\n\n */", Ok((_, _)));
}

#[test]
fn test_attribute_instance() {
    test!(
        attribute_instance,
        "(* full_case, parallel_case *)",
        Ok((_, _))
    );
    test!(attribute_instance, "(* full_case=1 *)", Ok((_, _)));
    test!(
        attribute_instance,
        "(* full_case=1, parallel_case = 0 *)",
        Ok((_, _))
    );
}

#[test]
fn test_expression() {
    test!(expression, "(!a ? 0 : !b : 1 : c ? 0 : 1)", Ok((_, _)));
}
