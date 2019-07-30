#![cfg(test)]

use crate::*;

macro_rules! test {
    ( $x:expr, $y:expr, $z:pat ) => {
        let info = SpanInfo::default();
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
    test!(
        data_declaration,
        "shortint s1, s2[0:9];",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "var byte my_byte;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "var v;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "var [15:0] vw;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "var enum bit { clear, error } status;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "var reg r;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "int i = 0;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "logic a;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "logic[3:0] v;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "logic signed [3:0] signed_reg;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "logic [-1:4] b;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "logic [4:0] x, y, z;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "int unsigned ui;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "int signed si;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "string myName = default_name;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "byte c = \"A\";",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "bit [10:0] b = \"x41\";",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "bit [1:4][7:0] h = \"hello\" ;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "event done;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "event done_too = done;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "event empty = null;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "typedef int intP;",
        Ok((_, DataDeclaration::TypeDeclaration(_)))
    );
    test!(
        data_declaration,
        "intP a, b;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "typedef enum type_identifier;",
        Ok((_, DataDeclaration::TypeDeclaration(_)))
    );
    test!(
        data_declaration,
        "typedef struct type_identifier;",
        Ok((_, DataDeclaration::TypeDeclaration(_)))
    );
    test!(
        data_declaration,
        "typedef union type_identifier;",
        Ok((_, DataDeclaration::TypeDeclaration(_)))
    );
    test!(
        data_declaration,
        "typedef class type_identifier;",
        Ok((_, DataDeclaration::TypeDeclaration(_)))
    );
    test!(
        data_declaration,
        "typedef interface class type_identifier;",
        Ok((_, DataDeclaration::TypeDeclaration(_)))
    );
    test!(
        data_declaration,
        "typedef type_identifier;",
        Ok((_, DataDeclaration::TypeDeclaration(_)))
    );
    test!(
        data_declaration,
        "typedef C::T c_t;",
        Ok((_, DataDeclaration::TypeDeclaration(_)))
    );
    test!(
        data_declaration,
        "enum {red, yellow, green} light1, light2;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "enum bit [1:0] {IDLE, XX='x, S1=2'b01, S2=2'b10} state, next;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "enum integer {IDLE, XX='x, S1='b01, S2='b10} state, next;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "enum integer {IDLE, XX='x, S1='b01, S2='b10} state, next;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "enum {bronze=3, silver, gold} medal;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "enum {a=3, b=7, c} alphabet;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "enum bit [3:0] {bronze='h3, silver, gold='h5} medal2;",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "integer i_array[*];",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "bit [20:0] array_b[string];",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "event ev_array[myClass];",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "int array_name [*];",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "int array_name1 [ integer ];",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "int a[int] = '{default:1};",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "byte q1[$];",
        Ok((_, DataDeclaration::Variable(_)))
    );
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
    test!(primary, "'0", Ok((_, Primary::PrimaryLiteral(_))));
    test!(primary, "10", Ok((_, Primary::PrimaryLiteral(_))));
    test!(primary, "\"aaa\"", Ok((_, Primary::PrimaryLiteral(_))));
    test!(primary, "this ", Ok((_, Primary::This(_))));
    test!(primary, "$ ", Ok((_, Primary::Dollar(_))));
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
fn test_comment() {
    test!(comment, "// comment", Ok((_, _)));
    test!(comment, "/* comment\n\n */", Ok((_, _)));
}

#[test]
fn test_expression() {
    test!(expression, "(!a ? 0 : !b : 1 : c ? 0 : 1)", Ok((_, _)));
}

#[test]
fn test_clause3() {
    test!(
        module_declaration,
        r##"module mux2to1 (input wire a, b, sel, // combined port and type declaration
                            output logic y);
              always_comb begin // procedural block
                if (sel) y = a; // procedural statement
                else y = b;
              end
            endmodule: mux2to1"##,
        Ok((_, _))
    );
    test!(
        program_declaration,
        r##"program test (input clk, input [16:1] addr, inout [7:0] data);
              initial begin
              end
            endprogram"##,
        Ok((_, _))
    );
    test!(
        module_declaration,
        r##"module memMod(simple_bus a); // simple_bus interface port
              logic avail;
              // When memMod is instantiated in module top, a.req is the req
              // signal in the sb_intf instance of the 'simple_bus' interface
              always @(posedge a.clk) a.gnt <= a.req & avail;
            endmodule"##,
        Ok((_, _))
    );
    test!(
        module_declaration,
        r##"module cpuMod(simple_bus b); // simple_bus interface port
            endmodule"##,
        Ok((_, _))
    );
    test!(
        module_declaration,
        r##"module top;
              logic clk = 0;
              simple_bus sb_intf(.clk(clk)); // Instantiate the interface
              memMod mem(.a(sb_intf)); // Connect interface to module instance
              cpuMod cpu(.b(sb_intf)); // Connect interface to module instance
            endmodule"##,
        Ok((_, _))
    );
    test!(
        package_declaration,
        r##"package ComplexPkg;
              typedef struct {
                shortreal i, r;
              } Complex;

              function Complex add(Complex a, b);
                add.r = a.r + b.r;
                add.i = a.i + b.i;
              endfunction

              function Complex mul(Complex a, b);
                mul.r = (a.r * b.r) - (a.i * b.i);
                mul.i = (a.r * b.i) + (a.i * b.r);
              endfunction
            endpackage : ComplexPkg"##,
        Ok((_, _))
    );
    test!(
        module_declaration,
        r##"module top; // module with no ports
              logic in1, in2, select; // variable declarations
              wire out1; // net declaration

              mux2to1 m1 (.a(in1), .b(in2), .sel(select), .y(out1)); // module instance

            endmodule: top"##,
        Ok((_, _))
    );
    test!(
        module_declaration,
        r##"module mux2to1 (input wire a, b, sel, // combined port and type declaration
                            output logic y);
              // netlist using built-in primitive instances
              not g1 (sel_n, sel);
              and g2 (a_s, a, sel_n);
              and g3 (b_s, b, sel);
              or g4 (y, a_s, b_s);
            endmodule: mux2to1"##,
        Ok((_, _))
    );
    test!(
        task_declaration,
        r##"task t;
              int b;
              b = 5 + $unit::b; // $unit::b is the one outside
            endtask"##,
        Ok((_, _))
    );
    test!(
        module_declaration,
        r##"module D;
              timeunit 100ps;
              timeprecision 10fs;
            endmodule"##,
        Ok((_, _))
    );
    test!(
        module_declaration,
        r##"module E;
              timeunit 100ps / 10fs; // timeunit with optional second argument
            endmodule"##,
        Ok((_, _))
    );
}

#[test]
fn test_clause4() {
    test!(
        module_declaration,
        r##"module test;
              logic a;
              initial begin
                a <= 0;
                a <= 1;
              end
            endmodule"##,
        Ok((_, _))
    );
    test!(
        module_declaration,
        r##"module test;
              assign p = q;
              initial begin
                q = 1;
                #1 q = 0;
                $display(p);
              end
            endmodule"##,
        Ok((_, _))
    );
}

#[test]
fn test_clause5() {
    test!(identifier, "shiftreg_a", Ok((_, _)));
    test!(identifier, "busa_index", Ok((_, _)));
    test!(identifier, "error_condition", Ok((_, _)));
    test!(identifier, "merge_ab", Ok((_, _)));
    test!(identifier, "_bus3", Ok((_, _)));
    test!(identifier, "n$657", Ok((_, _)));
    test!(identifier, "\\busa+index", Ok((_, _)));
    test!(identifier, "\\-clock", Ok((_, _)));
    test!(identifier, "\\***error-condition***", Ok((_, _)));
    test!(identifier, "\\net1/\\net2", Ok((_, _)));
    test!(identifier, "\\{a,b}", Ok((_, _)));
    test!(identifier, "\\a*(b+c)", Ok((_, _)));
    test!(
        subroutine_call_statement,
        "$display (\"display a message\");",
        Ok((_, _))
    );
    test!(subroutine_call_statement, "$finish;", Ok((_, _)));
    test!(primary, "'0", Ok((_, _)));
    test!(primary, "'1", Ok((_, _)));
    test!(primary, "'X", Ok((_, _)));
    test!(primary, "'x", Ok((_, _)));
    test!(primary, "'Z", Ok((_, _)));
    test!(primary, "'z", Ok((_, _)));
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
    test!(primary, "2.1ns ", Ok((_, Primary::PrimaryLiteral(_))));
    test!(primary, "40 ps ", Ok((_, Primary::PrimaryLiteral(_))));
    test!(
        subroutine_call_statement,
        r##"$display("Humpty Dumpty sat on a wall. \
            Humpty Dumpty had a great fall.");"##,
        Ok((_, _))
    );
    test!(
        subroutine_call_statement,
        r##"$display("Humpty Dumpty sat on a wall.\n\
            Humpty Dumpty had a great fall.");"##,
        Ok((_, _))
    );
    test!(module_item, r##"byte c1 = "A" ;"##, Ok((_, _)));
    test!(module_item, r##"bit [7:0] d = "\n" ;"##, Ok((_, _)));
    test!(
        module_item,
        r##"bit [8*12:1] stringvar = "Hello world\n";"##,
        Ok((_, _))
    );
    test!(
        module_item,
        r##"bit [0:11] [7:0] stringvar = "Hello world\n" ;"##,
        Ok((_, _))
    );
    test!(
        module_item,
        r##"byte c3 [0:12] = "hello world\n" ;"##,
        Ok((_, _))
    );
    test!(
        module_item,
        r##"typedef struct {int a; shortreal b;} ab;"##,
        Ok((_, _))
    );
    test!(module_item, r##"ab c;"##, Ok((_, _)));
    test!(
        module_item,
        r##"c = '{0, 0.0}; // structure literal type determined from
                           // the left-hand context (c)"##,
        Ok((_, _))
    );
    test!(
        module_item,
        r##"ab abarr[1:0] = '{'{1, 1.0}, '{2, 2.0}};"##,
        Ok((_, _))
    );
    test!(
        module_item,
        r##"c = '{a:0, b:0.0}; // member name and value for that member"##,
        Ok((_, _))
    );
    test!(
        module_item,
        r##"c = '{default:0}; // all elements of structure c are set to 0"##,
        Ok((_, _))
    );
    //TODO
    //test!(
    //    module_item,
    //    r##"d = ab'{int:1, shortreal:1.0}; // data type and default value for all
    //                                       // members of that type"##,
    //    Ok((_, _))
    //);
    test!(
        module_item,
        r##"ab abarr[1:0] = '{'{1, 1.0}, '{2, 2.0}};"##,
        Ok((_, _))
    );
    test!(
        module_declaration,
        r##"module test;
              struct {int X,Y,Z;} XYZ = '{3{1}};
              typedef struct {int a,b[4];} ab_t;
              int a,b,c;
              ab_t v1[1:0] [2:0];
              v1 = '{2{'{3{'{a,'{2{b,c}}}}}}};
            endmodule"##,
        Ok((_, _))
    );
    test!(
        module_item,
        r##"int n[1:2][1:3] = '{'{0,1,2},'{3{4}}};"##,
        Ok((_, _))
    );
    test!(
        module_item,
        r##"int n[1:2][1:6] = '{2{'{3{4, 5}}}}; // same as '{'{4,5,4,5,4,5},'{4,5,4,5,4,5}}"##,
        Ok((_, _))
    );
    test!(module_item, r##"typedef int triple [1:3];"##, Ok((_, _)));
    test!(
        module_item,
        r##"triple b = '{1:1, default:0}; // indices 2 and 3 assigned 0"##,
        Ok((_, _))
    );
    test!(
        attribute_instance,
        r##"(* full_case, parallel_case *)"##,
        Ok((_, _))
    );
    test!(attribute_instance, r##"(* full_case=1 *)"##, Ok((_, _)));
    test!(
        attribute_instance,
        r##"(* full_case, // no value assigned
               parallel_case=1 *)"##,
        Ok((_, _))
    );
    test!(attribute_instance, r##"(* full_case *)"##, Ok((_, _)));
    test!(
        attribute_instance,
        r##"(* full_case=1, parallel_case = 0 *)"##,
        Ok((_, _))
    );
    test!(
        module_item,
        r##"(* fsm_state *) logic [7:0] state1;"##,
        Ok((_, _))
    );
    test!(
        module_item,
        r##"(* fsm_state=1 *) logic [3:0] state2, state3;"##,
        Ok((_, _))
    );
    test!(
        module_item,
        r##"a = b + (* mode = "cla" *) c; // sets the value for the attribute mode
                                          // to be the string cla."##,
        Ok((_, _))
    );
    //TODO
    //test!(
    //    module_item,
    //    r##"a = add (* mode = "cla" *) (b, c);"##,
    //    Ok((_, _))
    //);
    test!(
        module_item,
        r##"a = b ? (* no_glitch *) c : d;"##,
        Ok((_, _))
    );
}
