#![cfg(test)]

use crate::*;

macro_rules! test {
    ( $x:expr, $y:expr, $z:pat ) => {
        nom_packrat::init!();
        let info = SpanInfo::default();
        let ret = all_consuming($x)(Span::new_extra($y, info));
        if let $z = ret {
        } else {
            assert!(false, "{:?}", ret)
        }
    };
}

mod unit {
    use super::*;

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
    fn test_inout_declaration() {
        test!(inout_declaration, "inout a", Ok((_, _)));
        test!(inout_declaration, "inout [7:0] a", Ok((_, _)));
        test!(inout_declaration, "inout signed [7:0] a", Ok((_, _)));
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
}

mod spec {
    use super::*;

    #[test]
    fn clause3() {
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
    fn clause4() {
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
    fn clause5() {
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
            many1(module_item),
            r##"typedef struct {int a; shortreal b;} ab;
                ab c;
                c = '{0, 0.0}; // structure literal type determined from
                               // the left-hand context (c)"##,
            Ok((_, _))
        );
        test!(
            module_item,
            r##"ab abarr[1:0] = '{'{1, 1.0}, '{2, 2.0}};"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"c = '{a:0, b:0.0};             // member name and value for that member
                c = '{default:0};              // all elements of structure c are set to 0
                d = ab'{int:1, shortreal:1.0}; // data type and default value for all
                                               // members of that type"##,
            Ok((_, _))
        );
        test!(
            module_item,
            r##"ab abarr[1:0] = '{'{1, 1.0}, '{2, 2.0}};"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"struct {int X,Y,Z;} XYZ = '{3{1}};
                typedef struct {int a,b[4];} ab_t;
                int a,b,c;
                ab_t v1[1:0] [2:0];
                v1 = '{2{'{3{'{a,'{2{b,c}}}}}}};"##,
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
            many1(module_item),
            r##"(* fsm_state *) logic [7:0] state1;
                (* fsm_state=1 *) logic [3:0] state2, state3;
                logic [3:0] reg1;                   // reg1 does NOT have fsm_state set
                (* fsm_state=0 *) logic [3:0] reg2; // nor does reg2"##,
            Ok((_, _))
        );
        test!(
            module_item,
            r##"a = b + (* mode = "cla" *) c; // sets the value for the attribute mode
                                              // to be the string cla."##,
            Ok((_, _))
        );
        test!(
            module_item,
            r##"a = add (* mode = "cla" *) (b, c);"##,
            Ok((_, _))
        );
        test!(
            module_item,
            r##"a = b ? (* no_glitch *) c : d;"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause6() {
        test!(
            many1(module_item),
            r##"trireg a;                         // trireg net of charge strength medium
                trireg (large) #(0,0,50) cap1;    // trireg net of charge strength large
                                                  // with charge decay time 50 time units
                trireg (small) signed [3:0] cap2; // signed 4-bit trireg vector of
                                                  // charge strength small"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"struct {
                  bit [7:0] A;
                  bit [7:0] B;
                  byte C;
                } abc;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"assign abc.C = sel ? 8'hBE : 8'hEF;

                not (abc.A[0],abc.B[0]),
                    (abc.A[1],abc.B[1]),
                    (abc.A[2],abc.B[2]),
                    (abc.A[3],abc.B[3]);

                always @(posedge clk) abc.B <= abc.B + 1;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"assign abc.C = sel ? 8'hDE : 8'hED;

                // Mixing continuous and procedural assignments to abc.A[3]
                always @(posedge clk) abc.A[7:3] <= !abc.B[7:3];"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"wire w = vara & varb;       // net with a continuous assignment

                logic v = consta & constb;  // variable with initialization

                logic vw;                   // no initial assignment
                assign vw = vara & varb;    // continuous assignment to a variable

                real circ;
                assign circ = 2.0 * PI * R; // continuous assignment to a variable"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef struct {
                  real field1;
                  bit field2;
                } T;

                // user-defined resolution function Tsum
                function automatic T Tsum (input T driver[]);
                  Tsum.field1 = 0.0;
                  foreach (driver[i])
                    Tsum.field1 += driver[i].field1;
                endfunction

                nettype T wT; // an unresolved nettype wT whose data type is T

                // a nettype wTsum whose data type is T and
                // resolution function is Tsum
                nettype T wTsum with Tsum;

                // user-defined data type TR
                typedef real TR[5];

                // an unresolved nettype wTR whose data type
                // is an array of real
                nettype TR wTR;

                // declare another name nettypeid2 for nettype wTsum
                nettype wTsum nettypeid2;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class Base #(parameter p = 1);
                  typedef struct {
                    real r;
                    bit[p-1:0] data;
                  } T;

                  static function T Tsum (input T driver[]);
                    Tsum.r = 0.0;
                    Tsum.data = 0;
                    foreach (driver[i])
                      Tsum.data += driver[i].data;
                    Tsum.r = $itor(Tsum.data);
                  endfunction
                endclass

                typedef Base#(32) MyBaseT;
                nettype MyBaseT::T narrowTsum with MyBaseT::Tsum;

                typedef Base#(64) MyBaseType;
                nettype MyBaseType::T wideTsum with MyBaseType::Tsum;

                narrowTsum net1; // data is 32 bits wide
                wideTsum net2; // data is 64 bits wide"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"package NetsPkg;
                  nettype real realNet;
                endpackage : NetsPkg

                module top();
                  interconnect [0:1] iBus;
                  lDriver l1(iBus[0]);
                  rDriver r1(iBus[1]);
                  rlMod m1(iBus);
                endmodule : top

                module lDriver(output wire logic out);
                endmodule : lDriver

                module rDriver
                  import NetsPkg::*;
                  (output realNet out);
                endmodule : rDriver

                module rlMod(input interconnect [0:1] iBus);
                  lMod l1(iBus[0]);
                  rMod r1(iBus[1]);
                endmodule : rlMod"##,
            Ok((_, _))
        );
        test!(
            library_text,
            r##"library realLib *.svr;
                library logicLib *.sv;

                config cfgReal;
                  design logicLib.top;
                  default liblist realLib logicLib;
                endconfig

                config cfgLogic;
                  design logicLib.top;
                  default liblist logicLib realLib;
                endconfig"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"module top();
                  interconnect [0:3] [0:1] aBus;
                  logic [0:3] dBus;
                  driver driverArray[0:3](aBus);
                  cmp cmpArray[0:3](aBus,rst,dBus);
                endmodule : top"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"package NetsPkg;
                  nettype real realNet;
                endpackage : NetsPkg"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"module driver
                  import NetsPkg::*;
                  #(parameter int delay = 30,
                              int iterations = 256)
                  (output realNet [0:1] out);
                  timeunit 1ns / 1ps;
                  real outR[1:0];
                  assign out = outR;
                  initial begin
                    outR[0] = 0.0;
                    outR[1] = 3.3;
                    for (int i = 0; i < iterations; i++) begin
                      #delay outR[0] += 0.2;
                      outR[1] -= 0.2;
                    end
                  end
                endmodule : driver"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"module driver #(parameter int delay = 30,
                                          int iterations = 256)
                               (output wire logic [0:1] out);
                  timeunit 1ns / 1ps;
                  logic [0:1] outvar;

                  assign out = outvar;

                  initial begin
                    outvar = '0;
                    for (int i = 0; i < iterations; i++)
                      #delay outvar++;
                  end
                endmodule : driver"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"module cmp
                  import NetsPkg::*;
                  #(parameter real hyst = 0.65)
                  (input realNet [0:1] inA,
                   input logic rst,
                   output logic out);
                  timeunit 1ns / 1ps;
                  real updatePeriod = 100.0;

                  initial out = 1'b0;

                  always #updatePeriod begin
                    if (rst) out <= 1'b0;
                    else if (inA[0] > inA[1]) out <= 1'b1;
                    else if (inA[0] < inA[1] - hyst) out <= 1'b0;
                  end
                endmodule : cmp"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"module cmp #(parameter real hyst = 0.65)
                            (input wire logic [0:1] inA,
                  input logic rst,
                  output logic out);

                  initial out = 1'b0;

                  always @(inA, rst) begin
                    if (rst) out <= 1'b0;
                    else if (inA[0] & ~inA[1]) out <= 1'b1;
                    else out <= 1'b0;
                  end
                endmodule : cmp"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"trireg (large) logic #(0,0,0) cap1;
                typedef logic [31:0] addressT;
                wire addressT w1;
                wire struct packed { logic ecc; logic [7:0] data; } memsig;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"wire w;         // equivalent to "wire logic w;"
                wire [15:0] ww; // equivalent to "wire logic [15:0] ww;""##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"tri reg r;
                inout wire reg p;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interconnect w1;             // legal
                interconnect [3:0] w2;       // legal
                interconnect [3:0] w3 [1:0]; // legal"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"nettype T wT;

                // a nettype wTsum whose data type is T and
                // resolution function is Tsum
                // Refer to example in 6.6.7 for the declaration of Tsum
                nettype T wTsum with Tsum;

                // a net of unresolved nettype wT
                wT w1;

                // an array of nets, each net element is of unresolved nettype wT
                wT w2[8];

                // a net of resolved nettype wTsum and resolution function Tsum
                wTsum w3;

                // an array of nets, each net is of resolved nettype wTsum
                wTsum w4[8];

                // user-defined data type TR which is an array of reals
                typedef real TR[5];

                // an unresolved nettype wTR with data type TR
                nettype TR wTR;

                // a net with unresolved nettype wTR and data type TR
                wTR w5;

                // an array of nets, each net has an unresolved nettype wTR
                // and data type TR
                wTR w6[8];"##,
            Ok((_, _))
        );
        test!(many1(module_item), r##"shortint s1, s2[0:9];"##, Ok((_, _)));
        test!(
            many1(module_item),
            r##"var byte my_byte; // equivalent to "byte my_byte;"
                var v;            // equivalent to "var logic v;"
                var [15:0] vw;    // equivalent to "var logic [15:0] vw;"
                var enum bit { clear, error } status;
                input var logic data_in;
                var reg r;"##,
            Ok((_, _))
        );
        test!(many1(module_item), r##"int i = 0;"##, Ok((_, _)));
        test!(
            many1(module_item),
            r##"wand w;                        // a scalar "wand" net
                tri [15:0] busa;               // a 16-bit bus
                trireg (small) storeit;        // a charge storage node of strength small
                logic a;                       // a scalar variable
                logic[3:0] v;                  // a 4-bit vector made up of (from most to
                                               // least significant)v[3], v[2], v[1], and v[0]
                logic signed [3:0] signed_reg; // a 4-bit vector in range -8 to 7
                logic [-1:4] b;                // a 6-bit vector
                wire w1, w2;                   // declares two nets
                logic [4:0] x, y, z;           // declares three 5-bit variables"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"tri1 scalared [63:0] bus64; //a bus that will be expanded
                tri vectored [31:0] data;   //a bus that may or may not be expanded"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int unsigned ui;
                int signed si;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"chandle variable_name ;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"parameter string default_name = "John Smith";
                string myName = default_name;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"byte c = "A";                // assigns to c "A"
                bit [10:0] b = "\x41";       // assigns to b 'b000_0100_0001
                bit [1:4][7:0] h = "hello" ; // assigns to h "ello""##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"string s0 = "String literal assign";// sets s0 to "String literal assign"
                string s1 = "hello\0world";         // sets s1 to "helloworld"
                bit [11:0] b = 12'ha41;
                string s2 = string'(b);             // sets s2 to 16'h0a41"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef logic [15:0] r_t;
                r_t r;
                integer i = 1;
                string b = "";
                string a = {"Hi", b};

                r = r_t'(a);    // OK
                b = string'(r); // OK
                b = "Hi";       // OK
                b = {5{"Hi"}};  // OK
                a = {i{"Hi"}};  // OK (non-constant replication)
                r = {i{"Hi"}};  // invalid (non-constant replication)
                a = {i{b}};     // OK
                a = {a,b};      // OK
                a = {"Hi",b};   // OK
                r = {"H",""};   // yields "H\0". "" is converted to 8'b0
                b = {"H",""};   // yields "H". "" is the empty string
                a[0] = "h";     // OK, same as a[0] = "cough"
                a[0] = b;       // invalid, requires a cast
                a[1] = "\0";    // ignored, a is unchanged"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"str = "123";
                int i = str.atoi(); // assigns 123 to i."##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"event done;            // declare a new event called done
                event done_too = done; // declare done_too as alias to done
                event empty = null;    // event variable with no synchronization object"##,
            Ok((_, _))
        );
        test!(many1(module_item), r##"typedef int intP;"##, Ok((_, _)));
        test!(many1(module_item), r##"intP a, b;"##, Ok((_, _)));
        test!(
            source_text,
            r##"interface intf_i;
                  typedef int data_t;
                endinterface

                module sub(intf_i p);
                  typedef p.data_t my_data_t;
                  my_data_t data;
                    // type of 'data' will be int when connected to interface above
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef enum type_identifier;
                typedef struct type_identifier;
                typedef union type_identifier;
                typedef class type_identifier;
                typedef interface class type_identifier;
                typedef type_identifier;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef C;
                C::T x;           // illegal; C is an incomplete forward type
                typedef C::T c_t; // legal; reference to C::T is made by a typedef
                c_t y;
                class C;
                  typedef int T;
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"enum {red, yellow, green} light1, light2; // anonymous int type"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"enum bit [1:0] {IDLE, XX='x, S1=2'b01, S2=2'b10} state, next;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"enum integer {IDLE, XX='x, S1='b01, S2='b10} state, next;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"enum integer {IDLE, XX='x, S1, S2} state, next;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"enum {bronze=3, silver, gold} medal; // silver=4, gold=5"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"enum {a=3, b=7, c} alphabet;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"enum {a=0, b=7, c, d=8} alphabet;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"enum {a, b=7, c} alphabet;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"enum bit [3:0] {bronze='h3, silver, gold='h5} medal2;

                // Correct declaration - bronze and gold sizes are redundant
                enum bit [3:0] {bronze=4'h3, silver, gold=4'h5} medal3;

                // Error in the bronze and gold member declarations
                enum bit [3:0] {bronze=5'h13, silver, gold=3'h5} medal4;

                // Error in c declaration, requires at least 2 bits
                enum bit [0:0] {a,b,c} alphabet;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef enum {NO, YES} boolean;
                boolean myvar; // named type"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef enum { add=10, sub[5], jmp[6:8] } E1;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"enum { register[2] = 1, register[2:4] = 10 } vr;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef enum { red, green, blue, yellow, white, black } Colors;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef enum { red, green, blue, yellow, white, black } Colors;

                Colors col;
                integer a, b;

                a = blue * 3;
                col = yellow;
                b = col + green;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef enum {Red, Green, Blue} Colors;
                typedef enum {Mo,Tu,We,Th,Fr,Sa,Su} Week;
                Colors C;
                Week W;
                int I;

                C = Colors'(C+1);            // C is converted to an integer, then added to
                                             // one, then converted back to a Colors type

                C = Colors'(Su);             // Legal; puts an out of range value into C

                I = C + W;                   // Legal; C and W are automatically cast to int"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  typedef enum { red, green, blue, yellow } Colors;
                  Colors c = c.first;
                  forever begin
                    $display( "%s : %d\n", c.name, c );
                    if( c == c.last ) break;
                    c = c.next;
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"localparam byte colon1 = ":" ;
                specparam delay = 10 ; // specparams are used for specify blocks
                parameter logic flag = 1 ;"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"class vector #(size = 1); // size is a parameter in a parameter port list
                  logic [size-1:0] v;
                endclass
                interface simple_bus #(AWIDTH = 64, type T = word) // parameter port list
                                      (input logic clk) ; // port list
                endinterface"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"module mc #(int N = 5, M = N*16, type T = int, T x = 0)
                ();
                endmodule"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"class Mem #(type T, int size);
                  T words[size];
                endclass

                typedef Mem#(byte, 1024) Kbyte;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"parameter msb = 7;       // defines msb as a constant value 7
                parameter e = 25, f = 9; // defines two constant numbers
                parameter r = 5.7;       // declares r as a real parameter
                parameter byte_size = 8,
                          byte_mask = byte_size - 1;
                parameter average_delay = (r + f) / 2;

                parameter signed [3:0] mux_selector = 0;
                parameter real r1 = 3.5e17;
                parameter p1 = 13'h7e;
                parameter [31:0] dec_const = 1'b1; // value converted to 32 bits
                parameter newconst = 3'h4;         // implied range of [2:0]
                parameter newconst = 4;            // implied range of at least [31:0]"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"parameter logic [31:0] P1 [3:0] = '{ 1, 2, 3, 4 } ; // unpacked array
                                                                    // parameter declaration"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"parameter r2 = $;
                property inq1(r1,r2);
                  @(posedge clk) a ##[r1:r2] b ##1 c |=> d;
                endproperty
                assert property (inq1(3, r2));"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface quiet_time_checker #(parameter min_quiet = 0,
                                               parameter max_quiet = 0)
                                              (input logic clk, reset_n, logic [1:0]en);

                  generate
                    if ( max_quiet == 0) begin
                      property quiet_time;
                        @(posedge clk) reset_n |-> ($countones(en) == 1);
                      endproperty
                      a1: assert property (quiet_time);
                    end
                    else begin
                      property quiet_time;
                        @(posedge clk)
                          (reset_n && ($past(en) != 0) && en == 0)
                          |->(en == 0)[*min_quiet:max_quiet]
                        ##1 ($countones(en) == 1);
                      endproperty
                      a1: assert property (quiet_time);
                    end
                    if ((min_quiet == 0) && ($isunbounded(max_quiet)))
                      $warning(warning_msg);
                  endgenerate
                endinterface

                quiet_time_checker #(0, 0) quiet_never (clk,1,enables);
                quiet_time_checker #(2, 4) quiet_in_window (clk,1,enables);
                quiet_time_checker #(0, $) quiet_any (clk,1,enables);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface width_checker #(parameter min_cks = 1, parameter max_cks = 1)
                                         (input logic clk, reset_n, expr);
                  generate
                    if ($isunbounded(max_cks)) begin
                      property width;
                        @(posedge clk)
                          (reset_n && $rose(expr)) |-> (expr [* min_cks]);
                      endproperty
                      a2: assert property (width);
                    end
                    else begin
                      property assert_width_p;
                        @(posedge clk)
                          (reset_n && $rose(expr)) |-> (expr[* min_cks:max_cks])
                            ##1 (!expr);
                      endproperty
                      a2: assert property (width);
                    end
                  endgenerate
                endinterface

                width_checker #(3, $) max_width_unspecified (clk,1,enables);
                width_checker #(2, 4) width_specified (clk,1,enables);"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"module ma #( parameter p1 = 1, parameter type p2 = shortint )
                           (input logic [p1:0] i, output logic [p1:0] o);
                  p2 j = 0; // type of j is set by a parameter, (shortint unless redefined)
                  always @(i) begin
                    o = i;
                    j++;
                  end
                endmodule
                module mb;
                  logic [3:0] i,o;
                  ma #(.p1(3), .p2(int)) u1(i,o); //redefines p2 to a type of int
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  specparam tRise_clk_q = 150, tFall_clk_q = 200;
                  specparam tRise_control = 40, tFall_control = 50;
                endspecify"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"module RAM16GEN ( output [7:0] DOUT,
                                  input [7:0] DIN,
                                  input [5:0] ADR,
                                  input WE, CE);
                  specparam dhold = 1.0;
                  specparam ddly = 1.0;
                  parameter width = 1;
                  parameter regsize = dhold + 1.0; // Illegal - cannot assign
                                                   // specparams to parameters
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"const logic option = a.b.c ;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"const class_name object = new(5,3);"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"module msl;
                  int st0;               // static
                  initial begin
                    int st1;             // static
                    static int st2;      // static
                    automatic int auto1; // automatic
                  end
                  task automatic t1();
                    int auto2;           // automatic
                    static int st3;      // static
                    automatic int auto3; // automatic
                  endtask
                endmodule"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"module top_legal;
                  int svar1 = 1;               // static keyword optional
                  initial begin
                    for (int i=0; i<3; i++) begin
                      automatic int loop3 = 0; // executes every loop
                      for (int j=0; j<3; j++) begin
                        loop3++;
                        $display(loop3);
                      end
                    end // prints 1 2 3 1 2 3 1 2 3
                    for (int i=0; i<3; i++) begin
                      static int loop2 = 0;    // executes once at time zero
                      for (int j=0; j<3; j++) begin
                        loop2++;
                        $display(loop2);
                      end
                    end // prints 1 2 3 4 5 6 7 8 9
                  end
                endmodule : top_legal

                module top_illegal;           // should not compile
                  initial begin
                    int svar2 = 2;            // static/automatic needed to show intent
                    for (int i=0; i<3; i++) begin
                      int loop3 = 0;          // illegal statement
                      for (int i=0; i<3; i++) begin
                        loop3++;
                        $display(loop3);
                      end
                    end
                  end
                endmodule : top_illegal"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"program automatic test ;
                  int i;            // not within a procedural block - static
                  task t ( int a ); // arguments and variables in t are automatic
                  endtask
                endprogram"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef bit node;    // 'bit' and 'node' are matching types
                typedef type1 type2; // 'type1' and 'type2' are matching types"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"struct packed {int A; int B;} AB1, AB2; // AB1, AB2 have matching types
                struct packed {int A; int B;} AB3; // the type of AB3 does not match
                                                   // the type of AB1"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef struct packed {int A; int B;} AB_t;
                AB_t AB1; AB_t AB2; // AB1 and AB2 have matching types

                typedef struct packed {int A; int B;} otherAB_t;
                otherAB_t AB3; // the type of AB3 does not match the type of AB1 or AB2"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef bit signed [7:0] BYTE; // matches the byte type
                typedef bit signed [0:7] ETYB; // does not match the byte type"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef byte MEM_BYTES [256];
                typedef bit signed [7:0] MY_MEM_BYTES [256]; // MY_MEM_BYTES matches
                                                             // MEM_BYTES

                typedef logic [1:0] [3:0] NIBBLES;
                typedef logic [7:0] MY_BYTE; // MY_BYTE and NIBBLES are not matching types

                typedef logic MD_ARY [][2:0];
                typedef logic MD_ARY_TOO [][0:2]; // Does not match MD_ARY"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef byte signed MY_CHAR; // MY_CHAR matches the byte type"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"struct {int A; int B;} AB1, AB2; // AB1, AB2 have equivalent types
                struct {int A; int B;} AB3;      // AB3 is not type equivalent to AB1"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef bit signed [7:0] BYTE; // equivalent to the byte type
                typedef struct packed signed {bit[3:0] a, b;} uint8;
                                               // equivalent to the byte type"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [9:0] A [0:5];
                bit [1:10] B [6];
                typedef bit [10:1] uint10;
                uint10 C [6:1];          // A, B and C have equivalent types
                typedef int anint [0:0]; // anint is not type equivalent to int"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"package p1;
                  typedef struct {int A;} t_1;
                endpackage

                typedef struct {int A;} t_2;

                module sub();
                  import p1::t_1;
                  parameter type t_3 = int;
                  parameter type t_4 = int;
                  typedef struct {int A;} t_5;
                  t_1 v1; t_2 v2; t_3 v3; t_4 v4; t_5 v5;
                endmodule

                module top();
                  typedef struct {int A;} t_6;
                  sub #(.t_3(t_6)) s1 ();
                  sub #(.t_3(t_6)) s2 ();

                  initial begin
                    s1.v1 = s2.v1; // legal - both types from package p1 (rule 8)
                    s1.v2 = s2.v2; // legal - both types from $unit (rule 4)
                    s1.v3 = s2.v3; // legal - both types from top (rule 2)
                    s1.v4 = s2.v4; // legal - both types are int (rule 1)
                    s1.v5 = s2.v5; // illegal - types from s1 and s2 (rule 4)
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"nettype nettypeid1 nettypeid2;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"var type(a+b) c, d;
                c = type(i+3)'(v[15:0]);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"localparam type T = type(bit[12:0]);"##,
            Ok((_, _))
        );
        // What is addfixed_int/add_float? UDP?
        //test!(
        //    many1(module_item),
        //    r##"bit [12:0] A_bus, B_bus;
        //        parameter type bus_t = type(A_bus);
        //        generate
        //          case (type(bus_t))
        //            type(bit[12:0]): addfixed_int #(bus_t) (A_bus,B_bus);
        //            type(real): add_float #(type(A_bus)) (A_bus,B_bus);
        //          endcase
        //        endgenerate"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"A = cast_t1'(expr_1) + cast_t2'(expr_2);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"cast_t1 temp1;
                cast_t2 temp2;

                temp1 = expr_1;
                temp2 = expr_2;
                A = temp1 + temp2;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [7:0] regA;
                logic signed [7:0] regS;

                regA = unsigned'(-4); // regA = 8'b11111100
                regS = signed'(4'b1100); // regS = -4"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef struct {
                  bit isfloat;
                  union { int i; shortreal f; } n; // anonymous type
                } tagged_st;                       // named structure

                typedef bit [$bits(tagged_st) - 1 : 0] tagbits; // tagged_st defined above

                tagged_st a [7:0];                 // unpacked array of structures

                tagbits t = tagbits'(a[3]);        // convert structure to array of bits
                a[4] = tagged_st'(t);              // convert array of bits back to structure"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  typedef enum { red, green, blue, yellow, white, black } Colors;
                  Colors col;
                  $cast( col, 2 + 3 );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  if ( ! $cast( col, 2 + 8 ) ) // 10: invalid cast
                    $display( "Error in cast" );
                end"##,
            Ok((_, _))
        );
        test!(many1(module_item), r##"col = Colors'(2 + 3);"##, Ok((_, _)));
        test!(many1(module_item), r##"B = dest_t'(A);"##, Ok((_, _)));
        test!(
            many1(module_item),
            r##"struct {bit[7:0] a; shortint b;} a;
                int b = int'(a);

                // Illegal conversion from 20-bit struct to int (32 bits) - run time error
                struct {bit a[$]; shortint b;} a = {{1,2,3,4}, 67};
                int b = int'(a);

                // Illegal conversion from int (32 bits) to struct dest_t (25 or 33 bits),
                // compile time error
                typedef struct {byte a[$]; bit b;} dest_t;
                int a;
                dest_t b = dest_t'(a);"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"typedef struct {
        //          shortint address;
        //          logic [3:0] code;
        //          byte command [2];
        //        } Control;

        //        typedef bit Bits [36:1];

        //        Control p;
        //        Bits stream[$];

        //        stream.push_back(Bits'(p)); // append packet to unpacked queue of Bits
        //        Bits b;
        //        Control q;
        //        b = stream.pop_front();     // get packet (as Bits) from stream
        //        q = Control'(b);            // convert packet bits back to a Control packet"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"typedef struct {
                  byte length;
                  shortint address;
                  byte payload[];
                  byte chksum;
                } Packet;"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"function Packet genPkt();
        //          Packet p;

        //          void'( randomize( p.address, p.length, p.payload )
        //            with { p.length > 1 && p.payload.size == p.length; } );
        //          p.chksum = p.payload.xor();
        //          return p;
        //        endfunction"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"typedef byte channel_type[$];
                channel_type channel;
                channel = {channel, channel_type'(genPkt())};"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"Packet p;
        //        int size;

        //        size = channel[0] + 4;
        //        p = Packet'( channel[0 : size - 1] ); // convert stream to Packet
        //        channel = channel[ size : $ ];        // update the stream so it now
        //                                              // lacks that packet"##,
        //    Ok((_, _))
        //);
        test!(
            source_text,
            r##"virtual class C#(parameter type T = logic, parameter SIZE = 1);
                  typedef logic [SIZE-1:0] t_vector;
                  typedef T t_array [SIZE-1:0];
                  typedef struct {
                    t_vector m0 [2*SIZE-1:0];
                    t_array m1;
                  } t_struct;
                endclass"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"module top ();
                  typedef logic [7:0] t_t0;
                  C#(t_t0,3)::t_vector v0;
                  C#(t_t0,3)::t_array a0;
                  C#(bit,4)::t_struct s0;
                endmodule"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause7() {
        //test!(
        //    many1(module_item),
        //    r##"struct { bit [7:0] opcode; bit [23:0] addr; }IR; // anonymous structure
        //                                                         // defines variable IR
        //        IR.opcode = 1; // set field in IR.

        //        typedef struct {
        //          bit [7:0] opcode;
        //          bit [23:0] addr;
        //        } instruction; // named structure type
        //        instruction IR; // define variable"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"struct packed signed {
                  int a;
                  shortint b;
                  byte c;
                  bit [7:0] d;
                } pack1; // signed, 2-state

                struct packed unsigned {
                  time a;
                  integer b;
                  logic [31:0] c;
                } pack2; // unsigned, 4-state"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef struct packed { // default unsigned
                  bit [3:0] GFC;
                  bit [7:0] VPI;
                  bit [11:0] VCI;
                  bit CLP;
                  bit [3:0] PT ;
                  bit [7:0] HEC;
                  bit [47:0] [7:0] Payload;
                  bit [2:0] filler;
                } s_atmcell;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef struct {
                  int addr = 1 + constant;
                  int crc;
                  byte data [4] = '{4{1}};
                } packet1;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"packet1 p1; // initialization defined by the typedef.
                            // p1.crc will use the default value for an int"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"packet1 pi = '{1,2,'{2,3,4,5}}; //suppresses the typedef initialization"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"typedef union { int i; shortreal f; } num; // named union type
        //        num n;
        //        n.f = 0.0; // set n in floating point format

        //        typedef struct {
        //          bit isfloat;
        //          union { int i; shortreal f; } n; // anonymous union type
        //        } tagged_st;                       // named structure"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"typedef union packed { // default unsigned
                  s_atmcell acell;
                  bit [423:0] bit_slice;
                  bit [52:0][7:0] byte_slice;
                } u_atmcell;

                u_atmcell u1;
                byte b; bit [3:0] nib;
                b = u1.bit_slice[415:408]; // same as b = u1.byte_slice[51];
                nib = u1.bit_slice [423:420]; // same as nib = u1.acell.GFC;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef union tagged {
                  void Invalid;
                  int Valid;
                } VInt;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef union tagged {
                  struct {
                    bit [4:0] reg1, reg2, regd;
                  } Add;
                  union tagged {
                    bit [9:0] JmpU;
                    struct {
                      bit [1:0] cc;
                      bit [9:0] addr;
                    } JmpC;
                  } Jmp;
                } Instr;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [7:0] c1; // packed array of scalar bit types
                real u [7:0]; // unpacked array of real types"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"byte c2;    // same as bit signed [7:0] c2;
                integer i1; // same as logic signed [31:0] i1;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int Array[0:7][0:31]; // array declaration using ranges

                int Array[8][32];     // array declaration using sizes"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [7:0] mema [0:255]; // declares a memory array of 256 8-bit
                                          // elements. The array indices are 0 to 255

                mema[5] = 0;              // Write to word at address 5

                data = mema[addr];        // Read word at address indexed by addr"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [3:0] [7:0] joe [1:10]; // 10 elements of 4 8-bit bytes
                                            // (each element packed into 32 bits)"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"joe[9] = joe[8] + 1; // 4 byte add
                joe[7][3:2] = joe[6][1:0]; // 2 byte copy"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [1:10] v1 [1:5];  // 1 to 10 varies most rapidly; compatible with memory arrays

                bit v2 [1:5] [1:10];  // 1 to 10 varies most rapidly, compatible with C

                bit [1:5] [1:10] v3 ; // 1 to 10 varies most rapidly

                bit [1:5] [1:6] v4 [1:7] [1:8]; // 1 to 6 varies most rapidly, followed by
                                                // 1 to 5, then 1 to 8 and then 1 to 7"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef bit [1:5] bsix;
                bsix [1:10] v5; // 1 to 5 varies most rapidly"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef bsix mem_type [0:3]; // array of four 'bsix' elements
                mem_type ba [0:7];           // array of eight 'mem_type' elements"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int A[2][3][4], B[2][3][4], C[5][4];
                A[0][2] = B[1][1]; // assign a subarray composed of four ints
                A[1] = B[0];       // assign a subarray composed of three arrays of
                                   // four ints each
                A = B;             // assign an entire array
                A[0][1] = C[4];    // assign compatible subarray of four ints"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [7:0] [31:0] v7 [1:5] [1:10], v8 [0:255]; // two arrays declared"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [63:0] data;
                logic [7:0] byte2;
                byte2 = data[23:16]; // an 8-bit part-select from data"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [3:0] [7:0] j; // j is a packed array
                byte k;
                k = j[2]; // select a single 8-bit element from j"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit signed [31:0] busA [7:0] ; // unpacked array of 8 32-bit vectors
                int busB [1:0];                // unpacked array of 2 integers
                busB = busA[7:6];              // select a 2-vector slice from busA"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int i = bitvec[j +: k]; // k must be constant.
                int a[x:y], b[y:z], e;
                a = {b[c -: d], e};     // d must be constant"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [3:0] nibble[]; // Dynamic array of 4-bit vectors
                integer mem[2][];   // Fixed-size unpacked array composed
                                    // of 2 dynamic subarrays of integers"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int arr1 [][2][3] = new [4]; // arr1 sized to length 4; elements are
                                             // fixed-size arrays and so do not require
                                             // initializing

                int arr2 [][] = new [4];     // arr2 sized to length 4; dynamic subarrays
                                             // remain unsized and uninitialized"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"int arr[2][][];
        //        arr[0] = new [4];    // dynamic subarray arr[0] sized to length 4

        //        arr[0][0] = new [2]; // legal, arr[0][n] created above for n = 0..3

        //        arr[1][0] = new [2]; // illegal, arr[1] not initialized so arr[1][0] does
        //                             // not exist

        //        arr[0][1][1] = new[2]; // illegal, arr[0][1][1] is an int, not a dynamic
        //                               // array"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"int idest[], isrc[3] = '{5, 6, 7};
        //        idest = new [3] (isrc); // set size and array element data values (5, 6, 7)"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"int src[3], dest1[], dest2[];
        //        src = '{2, 3, 4};
        //        dest1 = new[2] (src); // dest1's elements are {2, 3}.
        //        dest2 = new[4] (src); // dest2's elements are {2, 3, 4, 0}."##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"integer addr[];  // Declare the dynamic array.
        //        addr = new[100]; // Create a 100-element array.
        //        // Double the array size, preserving previous values.
        //        // Preexisting references to elements of addr are outdated.
        //        addr = new[200](addr);"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"int j = addr.size;
        //        addr = new[ addr.size() * 4 ] (addr); // quadruple addr array"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"int ab [] = new[ N ];      // create a temporary array of size N
        //        // use ab
        //        ab.delete;                 // delete the array contents
        //        $display( "%d", ab.size ); // prints 0"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"int A[10:1]; // fixed-size array of 10 elements
                int B[0:9];  // fixed-size array of 10 elements
                int C[24:1]; // fixed-size array of 24 elements
                A = B;       // ok. Compatible type and same size
                A = C;       // type check error: different sizes"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [7:0] V1[10:1];
                logic [7:0] V2[10];
                wire [7:0] W[9:0]; // data type is logic [7:0] W[9:0]
                assign W = V1;
                initial #10 V2 = W;"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"int A[2][100:1];
        //        int B[] = new[100]; // dynamic array of 100 elements
        //        int C[] = new[8];   // dynamic array of 8 elements
        //        int D [3][][];      // multidimensional array with dynamic subarrays
        //        D[2] = new [2];     // initialize one of D's dynamic subarrays
        //        D[2][0] = new [100];
        //        A[1] = B;           // OK. Both are arrays of 100 ints
        //        A[1] = C;           // type check error: different sizes (100 vs. 8 ints)
        //        A = D[2];           // A[0:1][100:1] and subarray D[2][0:1][0:99] both
        //                            // comprise 2 subarrays of 100 ints"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"int A[100:1];     // fixed-size array of 100 elements
        //        int B[];          // empty dynamic array
        //        int C[] = new[8]; // dynamic array of size 8

        //        B = A;            // ok. B has 100 elements
        //        B = C;            // ok. B has 8 elements"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"B = new[ C.size ] (C);"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"string d[1:5] = '{ "a", "b", "c", "d", "e" };
                string p[];
                p = { d[1:3], "hello", d[4:5] };"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int b[3:1][3:1];   // OK: same type, dimension, and size

                int b[1:3][0:2];   // OK: same type, dimension, & size (different ranges)

                logic b[3:1][3:1]; // error: incompatible element type

                event b[3:1][3:1]; // error: incompatible type

                int b[3:1];        // error: incompatible number of dimensions

                int b[3:1][4:1];   // error: incompatible size (3 vs. 4)"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"string b[4:1];       // OK: same type and size
                string b[5:2];       // OK: same type and size (different range)
                string b[] = new[4]; // OK: same type, number of dimensions, and
                                     // dimension size; requires run-time check"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"integer i_array[*];         // associative array of integer (unspecified
                                            // index)

                bit [20:0] array_b[string]; // associative array of 21-bit vector,
                                            // indexed by string

                event ev_array[myClass];    // associative array of event indexed by class
                                            // myClass"##,
            Ok((_, _))
        );
        test!(many1(module_item), r##"int array_name [*];"##, Ok((_, _)));
        test!(
            many1(module_item),
            r##"int array_name [ string ];"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int array_name [ some_Class ];"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int array_name1 [ integer ];
                typedef bit signed [4:1] SNibble;
                int array_name2 [ SNibble ];
                typedef bit [4:1] UNibble;
                int array_name3 [ UNibble ];"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef struct {byte B; int I[*];} Unpkt;
                int array_name [ Unpkt ];"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  int a[int] = '{default:1};
                  typedef struct { int x=1,y=2; } xy_t;
                  xy_t b[int];

                  begin
                    a[1]++;
                    b[2].x = 5;
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  int imem[int];
                  imem[ 3 ] = 1;
                  imem[ 16'hffff ] = 2;
                  imem[ 4'b1000 ] = 3;
                  $display( "%0d entries\n", imem.num ); // prints "3 entries"
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          int map[ string ];
        //          map[ "hello" ] = 1;
        //          map[ "sad" ] = 2;
        //          map[ "world" ] = 3;
        //          map.delete( "sad" ); // remove entry whose index is "sad" from "map"
        //          map.delete;          // remove all entries from the associative array "map"
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"initial begin
                  if ( map.exists( "hello" ))
                    map[ "hello" ] += 1;
                  else
                    map[ "hello" ] = 0;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string s;
                  if ( map.first( s ) )
                    $display( "First entry is : map[ %s ] = %0d\n", s, map[s] );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string s;
                  if ( map.last( s ) )
                    $display( "Last entry is : map[ %s ] = %0d\n", s, map[s] );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string s;
                  if ( map.first( s ) )
                    do
                      $display( "%s : %d\n", s, map[ s ] );
                    while ( map.next( s ) );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string s;
                  if ( map.last( s ) )
                    do
                      $display( "%s : %d\n", s, map[ s ] );
                    while ( map.prev( s ) );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string aa[int];
                  byte ix;
                  int status;
                  aa[ 1000 ] = "a";
                  status = aa.first( ix );
                    // status is –1
                    // ix is 232 (least significant 8 bits of 1000)
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"string words [int] = '{default: "hello"};

                // an associative array of 4-state integers indexed by strings, default is –1
                integer tab [string] = '{"Peter":20, "Paul":22, "Mary":23, default:-1 };"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"byte q1[$];                  // A queue of bytes
                string names[$] = { "Bob" }; // A queue of strings with one element
                integer Q[$] = { 3, 2, 7 };  // An initialized queue of integers
                bit q2[$:255];               // A queue whose maximum size is 256 bits"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef mytype element_t; // mytype is any legal type for a queue
                typedef element_t queue_t[$];
                element_t e;
                queue_t Q;
                int i;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  for ( int j = 0; j < Q.size; j++ ) $display( Q[j] );
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          int q[$] = { 2, 4, 8 };
        //          int e, pos;
        //          // assignment                    // method call yielding the
        //          //                               // same value in variable q
        //          // ----------------------------- // -------------------------
        //          q = { q, 6 };                    // q.push_back(6)
        //          q = { e, q };                    // q.push_front(e)
        //          q = q[1:$];                      // void'(q.pop_front()) or q.delete(0)
        //          q = q[0:$-1];                    // void'(q.pop_back()) or
        //                                           // q.delete(q.size-1)
        //          q = { q[0:pos-1], e, q[pos:$] }; // q.insert(pos, e)
        //          q = { q[0:pos], e, q[pos+1:$] }; // q.insert(pos+1, e)
        //          q = {};                          // q.delete()
        //        end"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          q = q[2:$];   // a new queue lacking the first two items
        //          q = q[1:$-1]; // a new queue lacking the first and last items
        //        end"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          string SA[10], qs[$];
        //          int IA[int], qi[$];

        //          // Find all items greater than 5
        //          qi = IA.find( x ) with ( x > 5 );
        //          qi = IA.find( x ); // shall be an error

        //          // Find indices of all items equal to 3
        //          qi = IA.find_index with ( item == 3 );

        //          // Find first item equal to Bob
        //          qs = SA.find_first with ( item == "Bob" );

        //          // Find last item equal to Henry
        //          qs = SA.find_last( y ) with ( y == "Henry" );

        //          // Find index of last item greater than Z
        //          qi = SA.find_last_index( s ) with ( s > "Z" );

        //          // Find smallest item
        //          qi = IA.min;

        //          // Find string with largest numerical value
        //          qs = SA.max with ( item.atoi );

        //          // Find all unique string elements
        //          qs = SA.unique;

        //          // Find all unique strings in lowercase
        //          qs = SA.unique( s ) with ( s.tolower );
        //        end"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          string s[] = { "hello", "sad", "world" };
        //          s.reverse;                              // s becomes { "world", "sad", "hello" };

        //          int q[$] = { 4, 5, 3, 1 };
        //          q.sort;                                 // q becomes { 1, 3, 4, 5 }

        //          struct { byte red, green, blue; } c [512];
        //          c.sort with ( item.red );               // sort c using the red field only
        //          c.sort( x ) with ( {x.blue, x.green} ); // sort by blue then green
        //        end"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          byte b[] = { 1, 2, 3, 4 };
        //          int y;
        //          y = b.sum ;                  // y becomes 10 => 1 + 2 + 3 + 4
        //          y = b.product ;              // y becomes 24 => 1 * 2 * 3 * 4
        //          y = b.xor with ( item + 4 ); // y becomes 12 => 5 ^ 6 ^ 7 ^ 8

        //          logic [7:0] m [2][2] = '{ '{5, 10}, '{15, 20} };
        //          int y;
        //          y = m.sum with (item.sum with (item)); // y becomes 50 => 5+10+15+20

        //          logic bit_arr [1024];
        //          int y;
        //          y = bit_arr.sum with ( int'(item) );   // forces result to be 32-bit
        //        end"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          int arr[];
        //          int q[$];

        //          // find all items equal to their position (index)
        //          q = arr.find with ( item == item.index );
        //        end"##,
        //    Ok((_, _))
        //);
    }

    #[test]
    fn clause8() {
        //test!(
        //    source_text,
        //    r##"class Packet ;
        //          //data or class properties
        //          bit [3:0] command;
        //          bit [40:0] address;
        //          bit [4:0] master_id;
        //          integer time_requested;
        //          integer time_issued;
        //          integer status;
        //          typedef enum { ERR_OVERFLOW = 10, ERR_UNDERFLOW = 1123} PCKT_TYPE;
        //          const integer buffer_size = 100;
        //          const integer header_size;

        //          // initialization
        //          function new();
        //            command = 4'd0;
        //            address = 41'b0;
        //            master_id = 5'bx;
        //            header_size = 10;
        //          endfunction

        //          // methods
        //          // public access entry points
        //          task clean();
        //            command = 0; address = 0; master_id = 5'bx;
        //          endtask

        //          task issue_request( int delay );
        //            // send request to bus
        //          endtask

        //          function integer current_status();
        //            current_status = status;
        //          endfunction
        //        endclass"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"Packet p; // declare a variable of class Packet
                p = new;  // initialize variable to a new allocated object
                          // of the class Packet"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class obj_example;
                endclass

                task task1(integer a, obj_example myexample);
                  if (myexample == null) myexample = new;
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  Packet p = new;
                  int var1;
                  p.command = INIT;
                  p.address = $random;
                  packet_time = p.time_requested;
                  var1 = p.buffer_size;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial $display (p.ERR_OVERFLOW);"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"class vector #(parameter width = 7, type T = int);
        //        endclass

        //        vector #(3) v = new;
        //        initial $display (vector #(3)::T'(3.45)); // Typecasting
        //        initial $display ((v.T)'(3.45)); //ILLEGAL
        //        initial $display (v.width);"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"Packet p = new;
                status = p.current_status();"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"status = current_status(p);"##,
            Ok((_, _))
        );
        test!(many1(module_item), r##"Packet p = new;"##, Ok((_, _)));
        //test!(
        //    many1(module_item),
        //    r##"class Packet;
        //          integer command;

        //          function new();
        //            command = IDLE;
        //          endfunction
        //        endclass"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"class C;
        //          int c1 = 1;
        //          int c2 = 1;
        //          int c3 = 1;
        //          function new(int a);
        //            c2 = 2;
        //            c3 = a;
        //          endfunction
        //        endclass

        //        class D extends C;
        //          int d1 = 4;
        //          int d2 = c2;
        //          int d3 = 6;
        //          function new;
        //            super.new(d3);
        //          endfunction
        //        endclass"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"Packet p = new(STARTUP, $random, $time);"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"function new(int cmd = IDLE, bit[12:0] adrs = 0, int cmd_time );
        //          command = cmd;
        //          address = adrs;
        //          time_requested = cmd_time;
        //        endfunction"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"class C; endclass
        //        class D extends C; endclass
        //        C c = D::new; // variable c of superclass type C now references
        //                      // a newly constructed object of type D"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"D d = new;
                C c = d;"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"class E #(type T = int) extends C;
        //          T x;
        //          function new(T x_init);
        //            super.new();
        //            x = x_init;
        //          endfunction
        //        endclass

        //        initial begin
        //          c = E #(.T(byte))::new(.x_init(5));
        //        end"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"class Packet ;
        //          static integer fileID = $fopen( "data", "r" );"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"Packet p;
                c = $fgetc( p.fileID );"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class id;
                  static int current = 0;
                  static function int next_id();
                    next_id = ++current; // OK to access static class property
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class TwoTasks;
                  static task t1(); endtask // static class method with
                                            // automatic variable lifetime

                  task static t2(); endtask // ILLEGAL: non-static class method with
                                            // static variable lifetime
                endclass"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"class Demo ;
        //          integer x;

        //          function new (integer x);
        //            this.x = x;
        //          endfunction
        //        endclass"##,
        //    Ok((_, _))
        //);
        test!(many1(module_item), r##"Packet p1;"##, Ok((_, _)));
        test!(many1(module_item), r##"p1 = new;"##, Ok((_, _)));
        test!(
            many1(module_item),
            r##"Packet p2;
                p2 = p1;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"Packet p1;
                Packet p2;
                p1 = new;
                p2 = new p1;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class baseA ;
                  integer j = 5;
                endclass

                class B ;
                  integer i = 1;
                  baseA a = new;
                endclass
                class xtndA extends baseA;
                  rand int x;
                  constraint cst1 { x < 10; }
                endclass

                function integer test;
                  xtndA xtnd1;
                  baseA base2, base3;
                  B b1 = new;        // Create an object of class B
                  B b2 = new b1;     // Create an object that is a copy of b1
                  b2.i = 10;         // i is changed in b2, but not in b1
                  b2.a.j = 50;       // change a.j, shared by both b1 and b2
                  test = b1.i;       // test is set to 1 (b1.i has not changed)
                  test = b1.a.j;     // test is set to 50 (a.j has changed)
                  xtnd1 = new;       // create a new instance of class xtndA
                  xtnd1.x = 3;
                  base2 = xtnd1;     // base2 refers to the same object as xtnd1
                  base3 = new base2; // Creates a shallow copy of xtnd1
                endfunction"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"Packet p1 = new;
        //        Packet p2 = new;
        //        p2.copy(p1);"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"class LinkedPacket;
                  Packet packet_c;
                  LinkedPacket next;

                  function LinkedPacket get_next();
                    get_next = next;
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class LinkedPacket extends Packet;
                  LinkedPacket next;

                  function LinkedPacket get_next();
                    get_next = next;
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"LinkedPacket lp = new;
                Packet p = lp;"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"class Packet;
        //          integer i = 1;
        //          function integer get();
        //            get = i;
        //          endfunction
        //        endclass

        //        class LinkedPacket extends Packet;
        //          integer i = 2;
        //          function integer get();
        //            get = -i;
        //          endfunction
        //        endclass

        //        LinkedPacket lp = new;
        //        Packet p = lp;
        //        j = p.i;     // j = 1, not 2
        //        j = p.get(); // j = 1, not -1 or –2"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"class Packet;                      // base class
                  integer value;
                  function integer delay();
                    delay = value * value;
                  endfunction
                endclass

                class LinkedPacket extends Packet; // derived class
                  integer value;
                  function integer delay();
                    delay = super.delay()+ value * super.value;
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"function new();
        //          super.new(5);
        //        endfunction"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"class Packet;
        //          local integer i;
        //          function integer compare (Packet other);
        //            compare = (this.i == other.i);
        //          endfunction
        //        endclass"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"class Jumbo_Packet;
        //          const int max_size = 9 * 1024; // global constant
        //          byte payload [];
        //          function new( int size );
        //            payload = new[ size > max_size ? max_size : size ];
        //          endfunction
        //        endclass"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"class Big_Packet;
        //          const int size; // instance constant
        //          byte payload [];
        //          function new();
        //            size = $urandom % 4096; //one assignment in new -> ok
        //            payload = new[ size ];
        //          endfunction
        //        endclass"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"class BasePacket;
        //          int A = 1;
        //          int B = 2;
        //          function void printA;
        //            $display("BasePacket::A is %d", A);
        //          endfunction : printA
        //          virtual function void printB;
        //            $display("BasePacket::B is %d", B);
        //          endfunction : printB
        //        endclass : BasePacket

        //        class My_Packet extends BasePacket;
        //          int A = 3;
        //          int B = 4;
        //          function void printA;
        //            $display("My_Packet::A is %d", A);
        //          endfunction: printA
        //          virtual function void printB;
        //            $display("My_Packet::B is %d", B);
        //          endfunction : printB
        //        endclass : My_Packet

        //        BasePacket P1 = new;
        //        My_Packet P2 = new;

        //        initial begin
        //          P1.printA; // displays 'BasePacket::A is 1'
        //          P1.printB; // displays 'BasePacket::B is 2'
        //          P1 = P2;   // P1 has a handle to a My_packet object
        //          P1.printA; // displays 'BasePacket::A is 1'
        //          P1.printB; // displays 'My_Packet::B is 4' – latest derived method
        //          P2.printA; // displays 'My_Packet::A is 3'
        //          P2.printB; // displays 'My_Packet::B is 4'
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"typedef int T; // T and int are matching data types.
                class C;
                  virtual function C some_method(int a); endfunction
                endclass

                class D extends C;
                  virtual function D some_method(T a); endfunction
                endclass

                class E #(type Y = logic) extends C;
                  virtual function D some_method(Y a); endfunction
                endclass

                E #() v1;    // Illegal: type parameter Y resolves to logic, which is not
                             // a matching type for argument a
                E #(int) v2; // Legal: type parameter Y resolves to int"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"virtual class BasePacket;
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"virtual class BasePacket;
                  pure virtual function integer send(bit[31:0] data); // No implementation
                endclass

                class EtherPacket extends BasePacket;
                  virtual function integer send(bit[31:0] data);
                    // body of the function
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"virtual function integer send(bit[31:0] data); // Will return 'x
        //        endfunction"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"BasePacket packets[100];"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"EtherPacket ep = new; // extends BasePacket
                TokenPacket tp = new; // extends BasePacket
                GPSPacket gp = new;   // extends EtherPacket
                packets[0] = ep;
                packets[1] = tp;
                packets[2] = gp;"##,
            Ok((_, _))
        );
        //test!(many1(module_item), r##"packets[1].send();"##, Ok((_, _)));
        //test!(
        //    many1(module_item),
        //    r##"class Base;
        //          typedef enum {bin,oct,dec,hex} radix;
        //          static task print( radix r, integer n ); ... endtask
        //        endclass

        //        Base b = new;
        //        int bin = 123;
        //        b.print( Base::bin, bin ); // Base::bin and bin are different
        //        Base::print( Base::hex, 66 );"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"class StringList;
                  class Node; // Nested class for a node in a linked list.
                    string name;
                    Node link;
                  endclass
                endclass

                class StringTree;
                  class Node; // Nested class for a node in a binary tree.
                    string name;
                    Node left, right;
                  endclass
                endclass
                // StringList::Node is different from StringTree::Node"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class Outer;
                  int outerProp;
                  local int outerLocalProp;
                  static int outerStaticProp;
                  static local int outerLocalStaticProp;
                  class Inner;
                    function void innerMethod(Outer h);
                      outerStaticProp = 0;
                        // Legal, same as Outer::outerStaticProp
                      outerLocalStaticProp = 0;
                        // Legal, nested classes may access local's in outer class
                      outerProp = 0;
                        // Illegal, unqualified access to non-static outer
                      h.outerProp = 0;
                        // Legal, qualified access.
                      h.outerLocalProp = 0;
                        // Legal, qualified access and locals to outer class allowed.
                    endfunction
                  endclass
                endclass"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"class Packet;
        //          Packet next;
        //          function Packet get_next();// single line
        //            get_next = next;
        //          endfunction

        //          // out-of-body (extern) declaration
        //          extern protected virtual function int send(int value);
        //        endclass

        //        function int Packet::send(int value);
        //          // dropped protected virtual, added Packet::
        //          // body of method
        //        endfunction"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"typedef real T;

        //        class C;
        //          typedef int T;
        //          extern function T f();
        //          extern function real f2();
        //        endclass

        //        function C::T C::f(); // the return must use the class scope resolution
        //                              // operator, since the type is defined within the
        //                              // class
        //          return 1;
        //        endfunction

        //        function real C::f2();
        //          return 1.0;
        //        endfunction"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"typedef int T;
        //        class C;
        //          extern function void f(T x);
        //          typedef real T;
        //        endclass

        //        function void C::f(T x);
        //        endfunction"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"class vector #(int size = 1);
                  bit [size-1:0] a;
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"vector #(10) vten;        // object with vector of size 10
                vector #(.size(2)) vtwo;  // object with vector of size 2
                typedef vector#(4) Vfour; // Class with vector of size 4"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class stack #(type T = int);
                  local T items[];
                  task push( T a ); endtask
                  task pop( ref T a ); endtask
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"stack is;             // default: a stack of ints
                stack#(bit[1:10]) bs; // a stack of 10-bit vectors
                stack#(real) rs;      // a stack of real numbers"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class vector #(int size = 1);
                  bit [size-1:0] a;
                  static int count = 0;
                  function void disp_count();
                    $display( "count: %d of size %d", count, size );
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef vector my_vector; // use default size of 1
                vector#(6) vx;            // use size 6"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef vector#(4) Vfour;
                typedef stack#(Vfour) Stack4;
                Stack4 s1, s2; // declare objects of type Stack4"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"class C #(type T = bit); endclass               // base class
        //        class D1 #(type P = real) extends C;            // T is bit (the default)
        //        class D2 #(type P = real) extends C #(integer); // T is integer
        //        class D3 #(type P = real) extends C #(P);       // T is P
        //        class D4 #(type P = C#(real)) extends P;        // for default, T is real"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"class C #(int p = 1);
                endclass
                class D #(int p);
                endclass
                C obj; // legal; equivalent to "C#() obj";
                D obj; // illegal; D has no default specialization"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"class C #(int p = 1);
        //          parameter int q = 5; // local parameter
        //          static task t;
        //            int p;
        //            int x = C::p; // C::p disambiguates p
        //                          // C::p is not p in the default specialization
        //          endtask
        //        endclass

        //        int x = C::p;     // illegal; C:: is not permitted in this context
        //        int y = C#()::p;  // legal; refers to parameter p in the default
        //                          // specialization of C
        //        typedef C T;      // T is a default specialization, not an alias to
        //                          // the name "C"
        //        int z = T::p;     // legal; T::p refers to p in the default specialization
        //        int v = C#(3)::p; // legal; parameter p in the specialization of C#(3)
        //        int w = C#()::q;  // legal; refers to the local parameter
        //        T obj = new();
        //        int u = obj.q;    // legal; refers to the local parameter
        //        bit arr[obj.q];   // illegal: local parameter is not a constant expression"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"class C #(int p = 1, type T = int);
        //          extern static function T f();
        //        endclass

        //        function C::T C::f();
        //          return p + C::p;
        //        endfunction

        //        initial $display("%0d %0d", C#()::f(),C#(5)::f()); // output is "2 10""##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"interface class A;
                endclass

                class B implements A;
                endclass

                class C extends B;
                endclass"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"interface class PutImp#(type PUT_T = logic);
        //          pure virtual function void put(PUT_T a);
        //        endclass

        //        interface class GetImp#(type GET_T = logic);
        //          pure virtual function GET_T get();
        //        endclass

        //        class Fifo#(type T = logic, int DEPTH=1) implements PutImp#(T), GetImp#(T);
        //          T myFifo [$:DEPTH-1];
        //          virtual function void put(T a);
        //            myFifo.push_back(a);
        //          endfunction
        //          virtual function T get();
        //            get = myFifo.pop_front();
        //          endfunction
        //        endclass

        //        class Stack#(type T = logic, int DEPTH=1) implements PutImp#(T), GetImp#(T);
        //          T myFifo [$:DEPTH-1];
        //          virtual function void put(T a);
        //            myFifo.push_front(a);
        //          endfunction
        //          virtual function T get();
        //            get = myFifo.pop_front();
        //          endfunction
        //        endclass"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"interface class PutImp#(type PUT_T = logic);
        //          pure virtual function void put(PUT_T a);
        //        endclass

        //        interface class GetImp#(type GET_T = logic);
        //          pure virtual function GET_T get();
        //        endclass

        //        class MyQueue #(type T = logic, int DEPTH = 1);
        //          T PipeQueue[$:DEPTH-1];
        //          virtual function void deleteQ();
        //            PipeQueue.delete();
        //          endfunction
        //        endclass

        //        class Fifo #(type T = logic, int DEPTH = 1)
        //            extends MyQueue#(T, DEPTH)
        //            implements PutImp#(T), GetImp#(T);
        //          virtual function void put(T a);
        //            PipeQueue.push_back(a);
        //          endfunction
        //          virtual function T get();
        //            get = PipeQueue.pop_front();
        //          endfunction
        //        endclass"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"virtual class XFifo#(type T_in = logic, type T_out = logic, int DEPTH = 1)
        //                             extends MyQueue#(T_out)
        //                             implements PutImp#(T_in), GetImp#(T_out);
        //          pure virtual function T_out translate(T_in a);
        //          virtual function void put(T_in a);
        //            PipeQueue.push_back(translate(a));
        //          endfunction
        //          virtual function T_out get();
        //            get = PipeQueue.pop_front();
        //          endfunction
        //        endclass"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"interface class IntfClass;
                  pure virtual function bit funcBase();
                  pure virtual function bit funcExt();
                endclass

                class BaseClass;
                  virtual function bit funcBase();
                    return (1);
                  endfunction
                endclass

                class ExtClass extends BaseClass implements IntfClass;
                  virtual function bit funcExt();
                    return (0);
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class IntfClass;
                  pure virtual function void f();
                endclass

                class BaseClass;
                  function void f();
                    $display("Called BaseClass::f()");
                  endfunction
                endclass

                class ExtClass extends BaseClass implements IntfClass;
                  virtual function void f();
                    $display("Called ExtClass::f()");
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class IntfA #(type T1 = logic);
                  typedef T1[1:0] T2;
                  pure virtual function T2 funcA();
                endclass : IntfA

                interface class IntfB #(type T = bit) extends IntfA #(T);
                  pure virtual function T2 funcB(); // legal, type T2 is inherited
                endclass : IntfB"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"interface class IntfC;
        //          typedef enum {ONE, TWO, THREE} t1_t;
        //          pure virtual function t1_t funcC();
        //        endclass : IntfC

        //        class ClassA implements IntfC;
        //          t1_t t1_i; // error, t1_t is not inherited from IntfC
        //          virtual function IntfC::t1_t funcC(); // correct
        //            return (IntfC::ONE); // correct
        //          endfunction : funcC
        //        endclass : ClassA"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"class Fifo #(type T = PutImp) implements T;
        //        virtual class Fifo #(type T = PutImp) implements T;
        //        interface class Fifo #(type T = PutImp) extends T;"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"typedef interface class IntfD;

        //        class ClassB implements IntfD #(bit); // illegal
        //          virtual function bit[1:0] funcD();
        //        endclass : ClassB

        //        // This interface class declaration must be declared before ClassB
        //        interface class IntfD #(type T1 = logic);
        //          typedef T1[1:0] T2;
        //          pure virtual function T2 funcD();
        //        endclass : IntfD"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"class Fifo #(type T = int) implements PutImp#(T), GetImp#(T);
                endclass
                Fifo#(int) fifo_obj = new;
                PutImp#(int) put_ref = fifo_obj;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  GetImp#(int) get_ref;
                  Fifo#(int) fifo_obj = new;
                  PutImp#(int) put_ref = fifo_obj;
                  $cast(get_ref, put_ref);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  $cast(fifo_obj, put_ref); // legal
                  $cast(put_ref, fifo_obj); // legal, but casting is not required
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"put_ref = new(); // illegal"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class IntfBase1;
                  pure virtual function bit funcBase();
                endclass

                interface class IntfBase2;
                  pure virtual function bit funcBase();
                endclass

                virtual class ClassBase;
                  pure virtual function bit funcBase();
                endclass

                class ClassExt extends ClassBase implements IntfBase1, IntfBase2;
                  virtual function bit funcBase();
                    return (0);
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class IntfBaseA;
                  pure virtual function bit funcBase();
                endclass

                interface class IntfBaseB;
                  pure virtual function string funcBase();
                endclass

                class ClassA implements IntfBaseA, IntfBaseB;
                  virtual function bit funcBase();
                    return (0);
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class PutImp#(type T = logic);
                  pure virtual function void put(T a);
                endclass

                interface class GetImp#(type T = logic);
                  pure virtual function T get();
                endclass

                interface class PutGetIntf#(type TYPE = logic)
                                            extends PutImp#(TYPE), GetImp#(TYPE);
                  typedef TYPE T;
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class IntfBase;
                  parameter SIZE = 64;
                endclass

                interface class IntfExt1 extends IntfBase;
                  pure virtual function bit funcExt1();
                endclass

                interface class IntfExt2 extends IntfBase;
                  pure virtual function bit funcExt2();
                endclass

                interface class IntfExt3 extends IntfExt1, IntfExt2;
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class IntfBase #(type T = int);
                  pure virtual function bit funcBase();
                endclass

                interface class IntfExt1 extends IntfBase#(bit);
                  pure virtual function bit funcExt1();
                endclass

                interface class IntfExt2 extends IntfBase#(logic);
                  pure virtual function bit funcExt2();
                endclass

                interface class IntfFinal extends IntfExt1, IntfExt2;
                  typedef bit T; // Override the conflicting identifier name
                  pure virtual function bit funcBase();
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class IntfClass;
                  pure virtual function bit funcA();
                  pure virtual function bit funcB();
                endclass

                // Partial implementation of IntfClass
                virtual class ClassA implements IntfClass;
                  virtual function bit funcA();
                    return (1);
                  endfunction
                  pure virtual function bit funcB();
                endclass

                // Complete implementation of IntfClass
                class ClassB extends ClassA;
                  virtual function bit funcB();
                    return (1);
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef class C2; // C2 is declared to be of type class
                class C1;
                  C2 c;
                endclass
                class C2;
                  C1 c;
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef class C ;
                module top ;
                  C#(1, real) v2 ; // positional parameter override
                  C#(.p(2), .T(real)) v3 ; // named parameter override
                endmodule

                class C #(parameter p = 2, type T = int);
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  myClass obj = new;
                  fork
                    task1( obj );
                    task2( obj );
                  join_none
                end"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause9() {
        test!(
            many1(module_item),
            r##"initial begin
                  a = 0; // initialize a
                  for (int index = 0; index < size; index++)
                    memory[index] = 0; // initialize memory word
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  inputs = 'b000000;     // initialize at time zero
                  #10 inputs = 'b011001; // first pattern
                  #10 inputs = 'b011011; // second pattern
                  #10 inputs = 'b011000; // third pattern
                  #10 inputs = 'b001000; // last pattern
                end"##,
            Ok((_, _))
        );
        test!(many1(module_item), r##"always areg = ~areg;"##, Ok((_, _)));
        test!(
            many1(module_item),
            r##"always #half_period areg = ~areg;"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"always_comb
        //          a = b & c;
        //        always_comb
        //          d <= #1ns b & c;"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"always_comb
                begin
                  a = b & c;
                  A1:assert (a != e) else if (!disable_error) $error("failed");
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always_latch
                  if(ck) q <= d;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always_ff @(posedge clock iff reset == 0 or posedge reset) begin
                  r1 <= reset ? 0 : r2 + 1;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"final
                  begin
                    $display("Number of cycles executed %d",$time/period);
                    $display("Final PC = %h",PC);
                  end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  areg = breg;
                  creg = areg; // creg stores the value of breg
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  areg = breg;
                  @(posedge clock) creg = areg; // assignment delayed until
                end                             // posedge on clock"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"parameter d = 50; // d declared as a parameter and
                logic [7:0] r;    // r declared as an 8-bit variable
                initial begin // a waveform controlled by sequential delays
                  #d r = 'h35;
                  #d r = 'hE2;
                  #d r = 'h00;
                  #d r = 'hF7;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork
                    #50 r = 'h35;
                    #100 r = 'hE2;
                    #150 r = 'h00;
                    #200 r = 'hF7;
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork
                    begin
                      statement1; // one process with 2 statements
                      statement2;
                    end
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork
                    begin
                      $display( "First Block\n" );
                      # 20ns;
                    end
                    begin
                      $display( "Second Block\n" );
                      @eventA;
                    end
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task wait_20;
                  fork
                    # 20;
                    return ; // Illegal: cannot return; task lives in another process
                  join_none
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial
                  for( int j = 1; j <= 3; ++j )
                    fork
                      automatic int k = j; // local copy, k, for each value of j
                      #k $write( "%0d", k );
                      begin
                        automatic int m = j; // the value of m is undetermined
                      end
                    join_none"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork
                    #200 r = 'hF7;
                    #150 r = 'h00;
                    #100 r = 'hE2;
                    #50 r = 'h35;
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork
                    @Aevent;
                    @Bevent;
                  join
                  areg = breg;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork
                    @enable_a
                      begin
                        #ta wa = 0;
                        #ta wa = 1;
                        #ta wa = 0;
                      end
                    @enable_b
                      begin
                        #tb wb = 1;
                        #tb wb = 0;
                        #tb wb = 1;
                      end
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin: blockB // block name after the begin or fork
                end: blockB"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  labelB: fork // label before the begin or fork
                  join_none : labelB
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  #10 rega = regb;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  #d rega = regb;         // d is defined as a parameter
                  #((d+e)/2) rega = regb; // delay is average of d and e
                  #regr regr = regr + 1;  // delay is the value in regr
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @r rega = regb;                       // controlled by any value change in the reg r
                  @(posedge clock) rega = regb;         // controlled by posedge on clock
                  forever @(negedge clock) rega = regb; // controlled by negedge on clock
                  forever @(edge clock) rega = regb;    // controlled by edge on clock
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"real AOR[];                       // dynamic array of reals
                byte stream[$];                   // queue of bytes
                initial wait(AOR.size() > 0);     // waits for array to be allocated
                initial wait($bits(stream) > 60); // waits for total number of bits
                                                  // in stream greater than 60

                Packet p = new; // Packet 1 -- Packet is defined in 8.2
                Packet q = new; // Packet 2
                initial fork
                  @(p.status); // Wait for status in Packet 1 to change
                  @p;          // Wait for a change to handle p
                  # 10 p = q;  // triggers @p.
                  // @(p.status) now waits for status in Packet 2 to change,
                  // if not already different from Packet 1
                join"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @(trig or enable) rega = regb; // controlled by trig or enable

                  @(posedge clk_a or posedge clk_b or trig) rega = regb;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(a, b, c, d, e);
                always @(posedge clk, negedge rstn);
                always @(a or b, c, d or e);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(*) // equivalent to @(a or b or c or d or f)
                    y = (a & b) | (c & d) | myfunction(f);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @* begin // equivalent to @(a or b or c or d or tmp1 or tmp2)
                  tmp1 = a & b;
                  tmp2 = c & d;
                  y = tmp1 | tmp2;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @* begin // equivalent to @(b)
                  @(i) kid = b; // i is not added to @*
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @* begin // equivalent to @(a or b or c or d)
                  x = a ^ b;
                  @*            // equivalent to @(c or d)
                  x = c ^ d;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @* begin // same as @(a or en)
                  y = 8'hff;
                  y[a] = !en;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @* begin // same as @(state or go or ws)
                  next = 4'b0;
                  case (1'b1)
                    state[IDLE]: if (go)  next[READ] = 1'b1;
                                 else     next[IDLE] = 1'b1;
                    state[READ]:          next[DLY ] = 1'b1;
                    state[DLY ]: if (!ws) next[DONE] = 1'b1;
                                 else     next[READ] = 1'b1;
                    state[DONE]:          next[IDLE] = 1'b1;
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module latch (output logic [31:0] y, input [31:0] a, input enable);
                  always @(a iff enable == 1)
                    y <= a; //latch is in transparent mode
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence abc;
                  @(posedge clk) a ##1 b ##1 c;
                endsequence

                program test;
                  initial begin
                    @ abc $display( "Saw a-b-c" );
                  end
                endprogram"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  wait (!enable) #10 a = b;
                  #10 c = d;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence abc;
                  @(posedge clk) a ##1 b ##1 c;
                endsequence

                sequence de;
                  @(negedge clk) d ##[2:5] e;
                endsequence

                program check;
                  initial begin
                    wait( abc.triggered || de.triggered );
                    if( abc.triggered )
                      $display( "abc succeeded" );
                    if( de.triggered )
                      $display( "de succeeded" );
                  end
                endprogram"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          repeat (3) @ (event_expression)
        //            // will execute event_expression three times
        //          repeat (-3) @ (event_expression)
        //            // will not execute event_expression.
        //          repeat (a) @ (event_expression)
        //            // if a is assigned -3, it will execute the event_expression if a is
        //            // declared as an unsigned variable, but not if a is signed
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"initial begin
                  fork
                    #5 a = b;
                    #5 b = a;
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork // data swap
                    a = #5 b;
                    b = #5 a;
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork // data shift
                    a = @(posedge clk) b;
                    b = @(posedge clk) c;
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  a <= repeat(5) @(posedge clk) data;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  a = repeat(num) @(clk) data;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  a <= repeat(a+b) @(posedge phi1 or negedge phi2) data;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  a <= repeat(a+b) @(edge phi1) data;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin : test
                  fork
                    child1();
                    child2();
                  join_none
                  do_test();
                end : test

                task do_test();
                  fork
                    child3();
                    child4();
                    fork : child5 // nested fork-join_none is a child process
                      descendant1();
                      descendant2();
                    join_none
                  join_none
                  do_sequence();
                  wait fork; // block until child1 ... child7 complete
                endtask

                function void do_sequence();
                  fork
                    child6();
                    child7();
                  join_none
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin : block_name
                  rega = regb;
                  disable block_name;
                  regc = rega; // this assignment will never execute
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin : block_name
                if (a == 0)
                  disable block_name;
                end // end of named block
                    // continue with code following named block"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m ();
                  always
                    begin : always1
                      t1: task1( ); // task call
                    end

                  always
                    begin
                      disable m.always1; // exit always1, which will exit task1,
                                         // if it was currently executing
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task proc_a;
                  begin
                    if (a == 0)
                      disable proc_a; // return if true
                  end
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin : outer_block
                  for (i = 0; i < n; i = i+1) begin : inner_block
                    @clk
                      if (a == 0) // "continue" loop
                        disable inner_block ;
                    @clk
                      if (a == b) // "break" from loop
                        disable outer_block;
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork
                    begin : event_expr
                      @ev1;
                      repeat (3) @trig;
                      #d action (areg, breg);
                    end
                    @reset disable event_expr;
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always begin : monostable
                  #250 q = 0;
                end

                always @retrig begin
                  disable monostable;
                  q = 1;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task get_first( output int adr );
                  fork
                    wait_device( 1, adr );
                    wait_device( 7, adr );
                    wait_device( 13, adr );
                  join_any
                  disable fork;
                endtask"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"class process;
        //          typedef enum { FINISHED, RUNNING, WAITING, SUSPENDED, KILLED } state;

        //          static function process self();
        //          function state status();
        //          function void kill();
        //          task await();
        //          function void suspend();
        //          function void resume();
        //          function void srandom( int seed );
        //          function string get_randstate();
        //          function void set_randstate( string state );
        //        endclass"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"task automatic do_n_way( int N );
        //          process job[] = new [N];

        //          foreach (job[j])
        //            fork
        //              automatic int k = j;
        //              begin job[k] = process::self(); ... ; end
        //            join_none

        //          foreach (job[j]) // wait for all processes to start
        //            wait( job[j] != null );
        //          job[1].await(); // wait for first process to finish

        //          foreach (job[j]) begin
        //            if ( job[j].status != process::FINISHED )
        //              job[j].kill();
        //          end
        //        endtask"##,
        //    Ok((_, _))
        //);
    }

    #[test]
    fn clause10() {
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          #1ns r = a;
        //          r = #1ns a;
        //          r <= #1ns a;
        //        end
        //        assign #2.5ns sum = a + b;"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"wire (strong1, pull0) mynet = enable;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"wire mynet ;
                assign (strong1, pull0) mynet = enable;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module adder (sum_out, carry_out, carry_in, ina, inb);
                  output [3:0] sum_out;
                  output carry_out;
                  input [3:0] ina, inb;
                  input carry_in;

                  wire carry_out, carry_in;
                  wire [3:0] sum_out, ina, inb;

                  assign {carry_out, sum_out} = ina + inb + carry_in;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module select_bus(busout, bus0, bus1, bus2, bus3, enable, s);
                  parameter n = 16;
                  parameter Zee = 16'bz;
                  output [1:n] busout;
                  input [1:n] bus0, bus1, bus2, bus3;
                  input enable;
                  input [1:2] s;

                  tri [1:n] data; // net declaration

                  // net declaration with continuous assignment
                  tri [1:n] busout = enable ? data : Zee;

                  // assignment statement with four continuous assignments
                  assign
                    data = (s == 0) ? bus0 : Zee,
                    data = (s == 1) ? bus1 : Zee,
                    data = (s == 2) ? bus2 : Zee,
                    data = (s == 3) ? bus3 : Zee;
                endmodule"##,
            Ok((_, _))
        );
        test!(many1(module_item), r##"wire #10 wireA;"##, Ok((_, _)));
        test!(
            many1(module_item),
            r##"initial begin
                  rega = 0;
                  rega[3] = 1;                // a bit-select
                  rega[3:5] = 7;              // a part-select
                  mema[address] = 8'hff;      // assignment to a mem element
                  {carry, acc} = rega + regb; // a concatenation
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module evaluates (out);
                  output out;
                  logic a, b, c;

                  initial begin
                    a = 0;
                    b = 1;
                    c = 0;
                  end

                  always c = #5 ~c;

                  always @(posedge c) begin
                    a <= b; // evaluates, schedules,
                    b <= a; // and executes in two steps
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module nonblock1;
                  logic a, b, c, d, e, f;

                  // blocking assignments
                  initial begin
                    a = #10 1; // a will be assigned 1 at time 10
                    b = #2 0; // b will be assigned 0 at time 12
                    c = #4 1; // c will be assigned 1 at time 16
                  end

                  // nonblocking assignments
                  initial begin
                    d <= #10 1; // d will be assigned 1 at time 10
                    e <= #2 0; // e will be assigned 0 at time 2
                    f <= #4 1; // f will be assigned 1 at time 4
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module nonblock2;
                  logic a, b;
                  initial begin
                    a = 0;
                    b = 1;
                    a <= b; // evaluates, schedules,
                    b <= a; // and executes in two steps
                  end

                  initial begin
                    $monitor ($time, ,"a = %b b = %b", a, b);
                    #100 $finish;
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module multiple;
                  logic a;
                  initial a = 1;
                    // The assigned value of the variable is determinate

                  initial begin
                    a <= #4 0; // schedules a = 0 at time 4
                    a <= #4 1; // schedules a = 1 at time 4
                  end          // At time 4, a = 1
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module multiple2;
                  logic a;

                  initial a = 1;
                  initial a <= #4 0; // schedules 0 at time 4
                  initial a <= #4 1; // schedules 1 at time 4

                  // At time 4, a = ??
                  // The assigned value of the variable is indeterminate
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module multiple3;
                  logic a;
                  initial #8 a <= #8 1;  // executed at time 8;
                                         // schedules an update of 1 at time 16
                  initial #12 a <= #4 0; // executed at time 12;
                                         // schedules an update of 0 at time 16

                  // Because it is determinate that the update of a to the value 1
                  // is scheduled before the update of a to the value 0,
                  // then it is determinate that a will have the value 0
                  // at the end of time slot 16.
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module multiple4;
                  logic r1;
                  logic [2:0] i;

                  initial begin
                    // makes assignments to r1 without cancelling previous assignments
                    for (i = 0; i <= 5; i++)
                      r1 <= # (i*10) i[0];
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"wire w = vara & varb;      // net with a continuous assignment

                logic v = consta & constb; // variable with initialization"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  force a = b + f(c) ;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module dff (q, d, clear, preset, clock);
                  output q;
                  input d, clear, preset, clock;
                  logic q;

                  always @(clear or preset)
                    if (!clear)
                      assign q = 0;
                    else if (!preset)
                      assign q = 1;
                    else
                      deassign q;

                  always @(posedge clock)
                    q = d;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module test;
                  logic a, b, c, d;
                  wire e;

                  and and1 (e, a, b, c);

                  initial begin
                    $monitor("%d d=%b,e=%b", $stime, d, e);
                    assign d = a & b & c;
                    a = 1;
                    b = 0;
                    c = 1;
                    #10;
                    force d = (a | b | c);
                    force e = (a | b | c);
                    #10;
                    release d;
                    release e;
                    #10 $finish;
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [5:0] a;
                logic signed [4:0] b;

                initial begin
                  a = 8'hff; // After the assignment, a = 6'h3f
                  b = 8'hff; // After the assignment, b = 5'h1f
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [0:5] a;
                logic signed [0:4] b, c;

                initial begin
                  a = 8'sh8f; // After the assignment, a = 6'h0f
                  b = 8'sh8f; // After the assignment, b = 5'h0f
                  c = -113;   // After the assignment, c = 15
                              // 1000_1111 = (-'h71 = -113) truncates to ('h0F = 15)
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [7:0] a;
                logic signed [7:0] b;
                logic signed [5:0] c, d;

                initial begin
                  a = 8'hff;
                  c = a;     // After the assignment, c = 6'h3f
                  b = -113;
                  d = b;     // After the assignment, d = 6'h0f
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  var int A[N] = '{default:1};
                  var integer i = '{31:1, 23:1, 15:1, 8:1, default:0};

                  typedef struct {real r, th;} C;
                  var C x = '{th:PI/2.0, r:1.0};
                  var real y [0:1] = '{0.0, 1.1}, z [0:9] = '{default: 3.1416};
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  var int B[4] = '{a, b, c, d};
                  var C y = '{1.0, PI/2.0};
                  '{a, b, c, d} = B;
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          typedef logic [1:0] [3:0] T;
        //          shortint'({T'{1,2}, T'{3,4}}) // yields 16'sh1234
        //        end"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          typedef byte U[3];
        //          var U A = '{1, 2, 3};
        //          var byte a, b, c;
        //          U'{a, b, c} = A;
        //          U'{c, a, b} = '{a+1, b+1, c+1};
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"initial begin
                  bit unpackedbits [1:0] = '{1,1};        // no size warning required as
                                                          // bit can be set to 1
                  int unpackedints [1:0] = '{1'b1, 1'b1}; // no size warning required as
                                                          // int can be set to 1'b1
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  unpackedbits = '{2 {y}} ;        // same as '{y, y}
                  int n[1:2][1:3] = '{2{'{3{y}}}}; // same as '{'{y,y,y},'{y,y,y}}
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial unpackedints = '{default:2}; // sets elements to 2"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  struct {int a; time b;} abkey[1:0];
                  abkey = '{'{a:1, b:2ns}, '{int:5, time:$time}};
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module mod1;

                  typedef struct {
                    int x;
                    int y;
                  } st;

                  st s1;
                  int k = 1;

                  initial begin
                    #1 s1 = '{1, 2+k};        // by position
                    #1 $display( s1.x, s1.y);
                    #1 s1 = '{x:2, y:3+k};    // by name
                    #1 $display( s1.x, s1.y);
                    #1 $finish;
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial s1 = '{default:2}; // sets x and y to 2"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"ab abkey[1:0] = '{'{a:1, b:1.0}, '{int:2, shortreal:2.0}};"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  struct {
                    int A;
                    struct {
                      int B, C;
                    } BC1, BC2;
                  } ABC, DEF;

                  ABC = '{A:1, BC1:'{B:2, C:3}, BC2:'{B:4,C:5}};
                  DEF = '{default:10};
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"typedef struct {
        //          logic [7:0] a;
        //          bit b;
        //          bit signed [31:0] c;
        //          string s;
        //        } sa;

        //        sa s2;
        //        initial s2 = '{int:1, default:0, string:""}; // set all to 0 except the
        //                                                     // array of bits to 1 and
        //                                                     // string to """##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"initial #10 s2 = '{default:'1, s : ""}; // set all to 1 except s to """##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  int A3[1:3];
                  A3 = {1, 2, 3}; // unpacked array concatenation: A3[1]=1, A3[2]=2, A3[3]=3
                  A3 = '{1, 2, 3}; // array assignment pattern: A3[1]=1, A3[2]=2, A3[3]=3
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  typedef int AI3[1:3];
                  AI3 A3;
                  int A9[1:9];

                  A3 = '{1, 2, 3};
                  A9 = '{3{A3}};                     // illegal, A3 is wrong element type
                  A9 = '{A3, 4, 5, 6, 7, 8, 9};      // illegal, A3 is wrong element type
                  A9 = {A3, 4, 5, A3, 6};            // legal, gives A9='{1,2,3,4,5,1,2,3,6}
                  A9 = '{9{1}};                      // legal, gives A9='{1,1,1,1,1,1,1,1,1}
                  A9 = {9{1}};                       // illegal, no replication in unpacked
                                                     // array concatenation
                  A9 = {A3, {4,5,6,7,8,9} };         // illegal, {...} is not self-determined here
                  A9 = {A3, '{4,5,6,7,8,9} };        // illegal, '{...} is not self-determined
                  A9 = {A3, 4, AI3'{5, 6, 7}, 8, 9}; // legal, A9='{1,2,3,4,5,6,7,8,9}
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string S, hello;
                  string SA[2];
                  byte B;
                  byte BA[2];

                  hello = "hello";

                  S = {hello, " world"};  // string concatenation: "hello world"
                  SA = {hello, " world"}; // array concatenation:
                                          // SA[0]="hello", SA[1]=" world"

                  B = {4'h6, 4'hf};       // vector concatenation: B=8'h6f
                  BA = {4'h6, 4'hf};      // array concatenation: BA[0]=8'h06, BA[1]=8'h0f
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string S1, S2;
                  typedef string T_SQ[$];
                  T_SQ SQ;

                  S1 = "S1";
                  S2 = "S2";
                  SQ = '{"element 0", "element 1"}; // assignment pattern, two strings
                  SQ = {S1, SQ, {"element 3 is ", S2} };
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  SQ = {S1, SQ, T_SQ'{"element 3 is ", S2} };
                    // result: '{"S1", "element 0", "element 1", "element 3 is ", "S2"}
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  typedef int T_QI[$];
                  T_QI jagged_array[$] = '{ {1}, T_QI'{2,3,4}, {5,6} };
                    // jagged_array[0][0] = 1 -- jagged_array[0] is a queue of 1 int
                    // jagged_array[1][0] = 2 -- jagged_array[1] is a queue of 3 ints
                    // jagged_array[1][1] = 3
                    // jagged_array[1][2] = 4
                    // jagged_array[2][0] = 5 -- jagged_array[2] is a queue of 2 ints
                    // jagged_array[2][1] = 6
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module byte_swap (inout wire [31:0] A, inout wire [31:0] B);
                  alias {A[7:0],A[15:8],A[23:16],A[31:24]} = B;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module byte_rip (inout wire [31:0] W, inout wire [7:0] LSB, MSB);
                  alias W[7:0] = LSB;
                  alias W[31:24] = MSB;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module overlap(inout wire [15:0] bus16, inout wire [11:0] low12, high12);
                  alias bus16[11:0] = low12;
                  alias bus16[15:4] = high12;
                endmodule

                module overlap(inout wire [15:0] bus16, inout wire [11:0] low12, high12);
                  alias bus16 = {high12, low12[3:0]};
                  alias high12[7:0] = low12[11:4];
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"alias bus16 = {high12[11:8], low12};
                alias bus16 = {high12, low12[3:0]};"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"alias bus16 = {high12, bus16[3:0]} = {bus16[15:12], low12};"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module lib1_dff(Reset, Clk, Data, Q, Q_Bar);
                endmodule

                module lib2_dff(reset, clock, data, q, qbar);
                endmodule

                module lib3_dff(RST, CLK, D, Q, Q_);
                endmodule

                module my_dff(rst, clk, d, q, q_bar); // wrapper cell
                  input rst, clk, d;
                  output q, q_bar;
                  alias rst = Reset = reset = RST;
                  alias clk = Clk = clock = CLK;
                  alias d = Data = data = D;
                  alias q = Q;
                  alias Q_ = q_bar = Q_Bar = qbar;
                  LIB_DFF my_dff (.*); // LIB_DFF is any of lib1_dff, lib2_dff or lib3_dff
                endmodule"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause11() {
        test!(
            many1(module_item),
            r##"initial begin
                  int IntA;
                  IntA = -12 / 3;      // The result is -4

                  IntA = -'d 12 / 3;   // The result is 1431655761

                  IntA = -'sd 12 / 3;  // The result is -4

                  IntA = -4'sd 12 / 3; // -4'sd12 is the negative of the 4-bit
                                       // quantity 1100, which is -4. -(-4) = 4
                                       // The result is 1
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  int n = 8, zero = 0;
                  int res = 'b01xz | n;      // res gets 'b11xz coerced to int, or 'b1100
                  int sum = n + n;           // sum gets 16 coerced to int, or 16
                  int sumx = 'x + n;         // sumx gets 'x coerced to int, or 0
                  int div2 = n/zero + n;     // div2 gets 'x coerced to int, or 0
                  integer div4 = n/zero + n; // div4 gets 'x
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          logic regA, regB, regC, result ;

        //          function logic myFunc(logic x);
        //          endfunction

        //          result = regA & (regB | myFunc(regC)) ;
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"initial begin
                  if ((a=b)) b = (a+=1);

                  a = (b = (c = 5));
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  a[i]+=2; // same as a[i] = a[i] +2;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  i = 10;
                  j = i++ + (i = i - 1);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  integer intS;
                  var logic [15:0] U;
                  var logic signed [15:0] S;

                  intS = -4'd12;
                  U = intS / 3;      // expression result is -4,
                                     // intS is an integer data type, U is 65532

                    U = -4'd12;      // U is 65524
                  intS = U / 3;      // expression result is 21841,
                                     // U is a logic data type

                  intS = -4'd12 / 3; // expression result is 1431655761.
                                     // -4'd12 is effectively a 32-bit logic data type

                  U = -12 / 3;       // expression result is -4, -12 is effectively
                                     // an integer data type. U is 65532

                  S = -12 / 3;       // expression result is -4. S is a signed logic

                  S = -4'sd12 / 3;   // expression result is 1. -4'sd12 is actually 4.
                                     // The rules for integer division yield 4/3==1
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  regA = alpha && beta; // regA is set to 0
                  regB = alpha || beta; // regB is set to 1
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module shift;
                  logic [3:0] start, result;
                  initial begin
                    start = 1;
                    result = (start << 2);
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module ashift;
                  logic signed [3:0] start, result;
                  initial begin
                    start = 4'b1000;
                    result = (start >>> 2);
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"wire [15:0] busa = drive_busa ? data : 16'bz;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  logic log1, log2, log3;
                  {log1, log2, log3} = 3'b111;
                  {log1, log2, log3} = {1'b1, 1'b1, 1'b1}; // same effect as 3'b111
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          byte a, b ;
        //          bit [1:0] c ;
        //          c = {a + b}[1:0]; // 2 lsb's of sum of a and b
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"parameter P = 32;

                // The following is legal for all P from 1 to 32

                assign b[31:0] = { {32-P{1'b1}}, a[P-1:0] } ;

                // The following is illegal for P=32 because the zero
                // replication appears alone within a concatenation

                assign c[31:0] = { {{32-P{1'b1}}}, a[P-1:0] };

                // The following is illegal for P=32

                initial
                  $displayb({32-P{1'b1}}, a[P-1:0]);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  result = {4{func(w)}} ;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  y = func(w) ;
                  result = {y, y, y, y} ;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string hello = "hello";
                  string s;
                  s = { hello, " ", "world" };
                  $display( "%s\n", s ); // displays 'hello world'
                  s = { s, " and goodbye" };
                  $display( "%s\n", s ); // displays 'hello world and goodbye'
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  int n = 3;
                  string s = {n { "boo " }};
                  $display( "%s\n", s ); // displays 'boo boo boo '
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          int a, b, c;
        //          if ( a inside {b, c} );
        //          int array [$] = '{3,4,5};
        //          if ( ex inside {1, 2, array} ); // same as { 1, 2, 3, 4, 5}
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"initial begin
                  logic [2:0] val;
                  while ( val inside {3'b1?1} ) ; // matches 3'b101, 3'b111, 3'b1x1, 3'b1z1
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          wire r;
        //          assign r=3'bz11 inside {3'b1?1, 3'b011}; // r = 1'bx
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"initial begin
                  bit ba = a inside { [16:23], [32:47] };
                  string I;
                  if (I inside {["a rock":"hard place"]});
                    // I between "a rock" and a "hard place"
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          int a, b, c;
        //          logic [10:0] up [3:0];
        //          logic [11:1] p1, p2, p3, p4;
        //          bit [96:1] y = {>>{ a, b, c }}; // OK: pack a, b, c
        //          int j = {>>{ a, b, c }};        // error: j is 32 bits < 96 bits
        //          bit [99:0] d = {>>{ a, b, c }}; // OK: d is padded with 4 bits
        //          {>>{ a, b, c }} = 23'b1;        // error: too few bits in stream
        //          {>>{ a, b, c }} = 96'b1;        // OK: unpack a = 0, b = 0, c = 1
        //          {>>{ a, b, c }} = 100'b11111;   // OK: unpack a = 0, b = 0, c = 1
        //                                          // 96 MSBs unpacked, 4 LSBs truncated
        //          { >> {p1, p2, p3, p4}} = up;    // OK: unpack p1 = up[3], p2 = up[2],
        //                                          // p3 = up[1], p4 = up[0]
        //        end"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          byte stream[$]; // byte stream

        //          class Packet;
        //            rand int header;
        //            rand int len;
        //            rand byte payload[];
        //            int crc;

        //            constraint G { len > 1; payload.size == len ; }

        //            function void post_randomize; crc = payload.sum; endfunction
        //          endclass

        //          send: begin // Create random packet and transmit
        //            byte q[$];
        //            Packet p = new;
        //            void'(p.randomize());
        //            q = {<< byte{p.header, p.len, p.payload, p.crc}}; // pack
        //            stream = {stream, q};                             // append to stream
        //          end

        //          receive: begin // Receive packet, unpack, and remove
        //            byte q[$];
        //            Packet p = new;
        //            {<< byte{ p.header, p.len, p.payload with [0 +: p.len], p.crc }} = stream;
        //            stream = stream[ $bits(p) / 8 : $ ]; // remove packet
        //          end
        //        end"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          q = {<<byte{p.header, p.len, p.payload with [0 +: p.len], p.crc}};
        //        end"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          q = {<<byte{p.header, p.len, p.payload with [0 : p.len-1], p.crc}};
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"initial begin
                  q = {<<byte{p}};
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  logic [31: 0] a_vect;
                  logic [0 :31] b_vect;
                  logic [63: 0] dword;
                  integer sel;

                  a = a_vect[ 0 +: 8]; // == a_vect[ 7 : 0]
                  a = a_vect[15 -: 8]; // == a_vect[15 : 8]

                  a = b_vect[ 0 +: 8]; // == b_vect[0 : 7]
                  a = b_vect[15 -: 8]; // == b_vect[8 :15]

                  a = dword[8*sel +: 8]; // variable part-select with fixed width
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [15:0] acc;
                logic [2:17] acc;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  logic [7:0] vect;
                  vect = 4; // fills vect with the pattern 00000100
                            // msb is bit 7, lsb is bit 0
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [7:0] mem_name[0:1023];"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [7:0] twod_array[0:255][0:255];
                wire threed_array[0:255][0:255][0:7];"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  localparam p = 7;
                  reg [7:0] m [5:1][5:1];
                  integer i;

                  a = m[1][i]; // longest static prefix is m[1]

                  a = m[p][1]; // longest static prefix is m[p][1]

                  a = m[i][1]; // longest static prefix is m
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  logic [15:0] a, b; // 16-bit variables
                  logic [15:0] sumA; // 16-bit variable
                  logic [16:0] sumB; // 17-bit variable

                  sumA = a + b;      // expression evaluates using 16 bits
                  sumB = a + b;      // expression evaluates using 17 bits
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  logic [15:0] a, b, answer; // 16-bit variables
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  answer = (a + b) >> 1; // will not work properly
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  answer = (a + b + 0) >> 1; // will work correctly
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module bitlength();
                  logic [3:0] a, b, c;
                  logic [4:0] d;

                  initial begin
                    a = 9;
                    b = 8;
                    c = 1;
                    $display("answer = %b", c ? (a&b) : d);
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [3:0] a;
                logic [5:0] b;
                logic [15:0] c;

                initial begin
                  a = 4'hF;
                  b = 6'hA;
                  $display("a*b=%h", a*b); // expression size is self-determined
                  c = {a**b};              // expression a**b is self-determined
                                           // due to concatenation operator {}
                  $display("a**b=%h", c);
                  c = a**b;                // expression size is determined by c
                  $display("c=%h", c);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  logic [7:0] regA, regB;
                  logic signed [7:0] regS;

                  regA = $unsigned(-4);                 // regA = 8'b11111100
                  regB = $unsigned(-4'sd4);             // regB = 8'b00001100
                  regS = $signed (4'b1100);             // regS = -4

                  regA = unsigned'(-4);                 // regA = 8'b11111100
                  regS = signed'(4'b1100);              // regS = -4

                  regS = regA + regB;                   // will do unsigned addition
                  regS = byte'(regA) + byte'(regB);     // will do signed addition
                  regS = signed'(regA) + signed'(regB); // will do signed addition
                  regS = $signed(regA) + $signed(regB); // will do signed addition
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [15:0] a;
                logic signed [7:0] b;

                initial
                  a = b[7:0]; // b[7:0] is unsigned and therefore zero-extended"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  typedef union tagged {
                    void Invalid;
                    int Valid;
                  } VInt;

                  VInt vi1, vi2;

                  vi1 = tagged Valid (23+34); // Create Valid int
                  vi2 = tagged Invalid;       // Create an Invalid value
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          typedef union tagged {
        //            struct {
        //              bit [4:0] reg1, reg2, regd;
        //            } Add;
        //            union tagged {
        //              bit [9:0] JmpU;
        //              struct {
        //                bit [1:0] cc;
        //                bit [9:0] addr;
        //              } JmpC;
        //            } Jmp;
        //          } Instr;

        //          Instr i1, i2;

        //          // Create an Add instruction with its 3 register fields
        //          i1 = ( e
        //            ? tagged Add '{ e1, 4, ed };                 // struct members by position
        //            : tagged Add '{ reg2:e2, regd:3, reg1:19 }); // by name (order irrelevant)

        //          // Create a Jump instruction, with "unconditional" sub-opcode
        //          i1 = tagged Jmp (tagged JmpU 239);

        //          // Create a Jump instruction, with "conditional" sub-opcode
        //          i2 = tagged Jmp (tagged JmpC '{ 2, 83 });         // inner struct by position
        //          i2 = tagged Jmp (tagged JmpC '{ cc:2, addr:83 }); // by name
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"initial begin
                  x = i1.Add.reg1;
                  i1.Add = '{19, 4, 3};
                  i1.Add.reg2 = 4;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module string_test;
                  bit [8*14:1] stringvar;

                  initial begin
                    stringvar = "Hello world";
                    $display("%s is stored as %h", stringvar, stringvar);
                    stringvar = {stringvar,"!!!"};
                    $display("%s is stored as %h", stringvar, stringvar);
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [8*10:1] s1, s2;
                initial begin
                  s1 = "Hello";
                  s2 = " world!";
                  if ({s1,s2} == "Hello world!")
                    $display("strings are equal");
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  a = (a:b:c) + (d:e:f);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  a = val - (32'd 50: 32'd 75: 32'd 100);
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"package pex_gen9_common_expressions;
        //          let valid_arb(request, valid, override) = |(request & valid) || override;
        //        endpackage

        //        module my_checker;
        //          import pex_gen9_common_expressions::*;
        //          logic a, b;
        //          wire [1:0] req;
        //          wire [1:0] vld;
        //          logic ovr;
        //          if (valid_arb(.request(req), .valid(vld), .override(ovr))) begin
        //          end
        //        endmodule"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"let mult(x, y) = ($bits(x) + $bits(y))'(x * y);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"let at_least_two(sig, rst = 1'b0) = rst || ($countones(sig) >= 2);
                logic [15:0] sig1;
                logic [3:0] sig2;
                always_comb begin
                  q1: assert (at_least_two(sig1));
                  q2: assert (at_least_two(~sig2));
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          task write_value;
        //            input logic [31:0] addr;
        //            input logic [31:0] value;
        //          endtask

        //          let addr = top.block1.unit1.base + top.block1.unit2.displ;

        //          write_value(addr, 0);
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"module m;
                  logic clk, a, b;
                  logic p, q, r;

                  // let with formal arguments and default value on y
                  let eq(x, y = b) = x == y;

                  // without parameters, binds to a, b above
                  let tmp = a && b;

                  a1: assert property (@(posedge clk) eq(p,q));
                  always_comb begin
                    a2: assert (eq(r)); // use default for y
                    a3: assert (tmp);
                  end
                endmodule : m"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m;
                  bit clk, a, b;
                  logic p, q, r;
                  // let eq(x, y = b) = x == y;
                  // let tmp = a && b;

                  a1: assert property (@(posedge clk) (m.p == m.q));
                  always_comb begin
                    a2: assert ((m.r == m.b)); // use default for y
                    a3: assert ((m.a && m.b));
                  end
                endmodule : m"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  logic x = 1'b1;
                  logic a, b;
                  let y = x;

                  always_comb begin
                    // y binds to preceding definition of x
                    // in the declarative context of let
                    bit x = 1'b0;
                    b = a | y;
                  end
                endmodule : top"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  bit x = 1'b1;
                  bit a;
                  // let y = x;

                  always_comb begin
                    // y binds to preceding definition of x
                    // in the declarative context of let
                    bit x = 1'b0;
                    b = a | (top.x);
                  end
                endmodule : top"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  logic a, b;
                  let x = a || b;
                  sequence s;
                    x ##1 b;
                  endsequence : s
                endmodule : top"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  logic a, b;
                  // let x = a || b;
                  sequence s;
                    (top.a || top.b) ##1 b;
                  endsequence : s
                endmodule : top"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"module m();
        //          wire a, b;
        //          wire [2:0] c;
        //          wire [2:0] d;
        //          wire e;

        //          for (genvar i = 0; i < 3; i++) begin : L0
        //            if (i !=1) begin : L1
        //              let my_let(x) = !x || b && c[i];
        //              s1: assign d[2 – i] = my_let(a)); // OK
        //            end : L1
        //          end : L0
        //          s2: assign e = L0[0].L1.my_let(a)); // Illegal
        //        endmodule : m"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"assign d[2] = (!m.a || m.b && m.c[0]);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"assign d[0] = (!m.a || m.b && m.c[2]);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m(input clock);
                  logic [15:0] a, b;
                  logic c, d;
                  typedef bit [15:0] bits;

                  let ones_match(bits x, y) = x == y;
                  let same(logic x, y) = x === y;

                  always_comb
                    a1: assert(ones_match(a, b));

                  property toggles(bit x, y);
                    same(x, y) |=> !same(x, y);
                  endproperty

                  a2: assert property (@(posedge clock) toggles(c, d));
                endmodule : m"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m(input clock);
                  logic [15:0] a, b;
                  logic c, d;
                  typedef bit [15:0] bits;

                  // let ones_match(bits x, y) = x == y;
                  // let same(logic x, y) = x === y;

                  always_comb
                    a1:assert((bits'(a) == bits'(b)));

                  property toggles(bit x, y);
                    (logic'(x) === logic'(y)) |=> ! (logic'(x) === logic'(y));
                  endproperty

                  a2: assert property (@(posedge clock) toggles(c, d));
                  endmodule : m"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"module m(input clock);
        //          logic a;
        //          let p1(x) = $past(x);
        //          let p2(x) = $past(x,,,@(posedge clock));
        //          let s(x) = $sampled(x);
        //          always_comb begin
        //            a1: assert(p1(a));
        //            a2: assert(p2(a));
        //            a3: assert(s(a));
        //          end
        //          a4: assert property(@(posedge clock) p1(a));
        //        endmodule : m"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"module m(input clock);
        //          logic a;
        //          let p1(x) = $past(x);
        //          let p2(x) = $past(x,,,@(posedge clock));
        //          let s(x) = $sampled(x);
        //          always_comb begin
        //            a1: assert(($past(a))); // Illegal: no clock can be inferred
        //            a2: assert(($past(a,,,@(posedge clock))));
        //            a3: assert(($sampled (a)));
        //          end
        //          a4: assert property(@(posedge clock)($past(a))); // @(posedge clock)
        //                                                           // is inferred
        //        endmodule : m"##,
        //    Ok((_, _))
        //);
    }

    #[test]
    fn clause12() {
        test!(
            many1(module_item),
            r##"initial begin
                  if (index > 0)
                    if (rega > regb)
                      result = rega;
                    else // else applies to preceding if
                      result = regb;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  if (index > 0)
                    begin
                      if (rega > regb)
                        result = rega;
                    end
                  else result = regb;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  // declare variables and parameters
                  logic [31:0] instruction,
                               segment_area[255:0];
                  logic [7:0]  index;
                  logic [5:0]  modify_seg1,
                               modify_seg2,
                               modify_seg3;
                  parameter
                    segment1 = 0, inc_seg1 = 1,
                    segment2 = 20, inc_seg2 = 2,
                    segment3 = 64, inc_seg3 = 4,
                    data = 128;

                  // test the index variable
                  if (index < segment2) begin
                    instruction = segment_area [index + modify_seg1];
                    index = index + inc_seg1;
                  end
                  else if (index < segment3) begin
                    instruction = segment_area [index + modify_seg2];
                    index = index + inc_seg2;
                  end
                  else if (index < data) begin
                    instruction = segment_area [index + modify_seg3];
                    index = index + inc_seg3;
                  end
                  else
                    instruction = segment_area [index];
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  unique if ((a==0) || (a==1)) $display("0 or 1");
                  else if (a == 2) $display("2");
                  else if (a == 4) $display("4"); // values 3,5,6,7 cause a violation report

                  priority if (a[2:1]==0) $display("0 or 1");
                  else if (a[2] == 0) $display("2 or 3");
                  else $display("4 to 7"); // covers all other possible values,
                                           // so no violation report
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  unique0 if ((a==0) || (a==1)) $display("0 or 1");
                  else if (a == 2) $display("2");
                  else if (a == 4) $display("4"); // values 3,5,6,7
                                                  // cause no violation report
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always_comb begin
                  not_a = !a;
                end

                always_comb begin : a1
                  u1: unique if (a)
                    z = a | b;
                  else if (not_a)
                    z = a | c;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always_comb begin
                  for (int j = 0; j < 3; j++)
                  not_a[j] = !a[j];
                end

                always_comb begin : a1
                  for (int j = 0; j < 3; j++)
                    unique if (a[j])
                      z[j] = a[j] | b[j];
                    else if (not_a[j])
                      z[j] = a[j] | c[j];
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"module fsm();
        //          function bit f1(bit a, bit not_a)
        //            a1: unique if (a)
        //            else if (not_a)
        //          endfunction

        //          always_comb begin : b1
        //            some_stuff = f1(c, d);
        //          end

        //          always_comb begin : b2
        //            other_stuff = f1(e, f);
        //          end
        //        endmodule"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"initial begin
                  logic [15:0] data;
                  logic [9:0] result;
                  case (data)
                    16'd0: result = 10'b0111111111;
                    16'd1: result = 10'b1011111111;
                    16'd2: result = 10'b1101111111;
                    16'd3: result = 10'b1110111111;
                    16'd4: result = 10'b1111011111;
                    16'd5: result = 10'b1111101111;
                    16'd6: result = 10'b1111110111;
                    16'd7: result = 10'b1111111011;
                    16'd8: result = 10'b1111111101;
                    16'd9: result = 10'b1111111110;
                    default result = 'x;
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  case (select[1:2])
                    2'b00: result = 0;
                    2'b01: result = flaga;
                    2'b0x,
                    2'b0z: result = flaga ? 'x : 0;
                    2'b10: result = flagb;
                    2'bx0,
                    2'bz0: result = flagb ? 'x : 0;
                    default result = 'x;
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  case (sig)
                    1'bz: $display("signal is floating");
                    1'bx: $display("signal is unknown");
                    default: $display("signal is %b", sig);
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  logic [7:0] ir;

                  casez (ir)
                    8'b1???????: instruction1(ir);
                    8'b01??????: instruction2(ir);
                    8'b00010???: instruction3(ir);
                    8'b000001??: instruction4(ir);
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  logic [7:0] r, mask;

                  mask = 8'bx0x0x0x0;
                  casex (r ^ mask)
                    8'b001100xx: stat1;
                    8'b1100xx00: stat2;
                    8'b00xx0011: stat3;
                    8'bxx010100: stat4;
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  logic [2:0] encode ;

                  case (1)
                    encode[2] : $display("Select Line 2") ;
                    encode[1] : $display("Select Line 1") ;
                    encode[0] : $display("Select Line 0") ;
                    default $display("Error: One of the bits expected ON");
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  bit [2:0] a;
                  unique case(a) // values 3,5,6,7 cause a violation report
                    0,1: $display("0 or 1");
                    2: $display("2");
                    4: $display("4");
                  endcase

                  priority casez(a) // values 4,5,6,7 cause a violation report
                    3'b00?: $display("0 or 1");
                    3'b0??: $display("2 or 3");
                  endcase

                  unique0 case(a) // values 3,5,6,7 do not cause a violation report
                    0,1: $display("0 or 1");
                    2: $display("2");
                    4: $display("4");
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always_comb begin
                  not_a = !a;
                end

                always_comb begin : a1
                  unique case (1'b1)
                    a : z = b;
                    not_a : z = c;
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [2:0] status;
                always @(posedge clock)
                  priority case (status) inside
                  1, 3 : task1; // matches 'b001 and 'b011
                  3'b0?0, [4:7]: task2; // matches 'b000 'b010 'b0x0 'b0z0
                                        // 'b100 'b101 'b110 'b111
                  endcase // priority case fails all other values including
                          // 'b00x 'b01x 'bxxx"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  typedef union tagged {
                    void Invalid;
                    int Valid;
                  } VInt;

                  VInt v;

                  case (v) matches
                    tagged Invalid : $display ("v is Invalid");
                    tagged Valid .n : $display ("v is Valid with value %d", n);
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  typedef union tagged {
                    struct {
                      bit [4:0] reg1, reg2, regd;
                    } Add;
                    union tagged {
                      bit [9:0] JmpU;
                      struct {
                        bit [1:0] cc;
                        bit [9:0] addr;
                      } JmpC;
                    } Jmp;
                  } Instr;

                  Instr instr;

                  case (instr) matches
                    tagged Add '{.r1, .r2, .rd} &&& (rd != 0) : rf[rd] = rf[r1] + rf[r2];
                    tagged Jmp .j : case (j) matches
                                      tagged JmpU .a : pc = pc + a;
                                      tagged JmpC '{.c, .a}: if (rf[c]) pc = a;
                                    endcase
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  case (instr) matches
                    tagged Add '{.*, .*, 0} : ; // no op
                    tagged Add '{.r1, .r2, .rd} : rf[rd] = rf[r1] + rf[r2];
                    tagged Jmp .j : case (j) matches
                                      tagged JmpU .a : pc = pc + a;
                                      tagged JmpC '{.c, .a} : if (rf[c]) pc = a;
                                    endcase
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  case (instr) matches
                    tagged Add s: case (s) matches
                                    '{.*, .*, 0} : ; // no op
                                    '{.r1, .r2, .rd} : rf[rd] = rf[r1] + rf[r2];
                                  endcase
                    tagged Jmp .j: case (j) matches
                                     tagged JmpU .a : pc = pc + a;
                                     tagged JmpC '{.c, .a} : if (rf[c]) pc = a;
                                   endcase
                  endcase
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          case (instr) matches
        //            tagged Add '{.r1, .r2, .rd} &&& (rd != 0) : rf[rd] = rf[r1] + rf[r2];
        //            tagged Jmp (tagged JmpU .a) : pc = pc + a;
        //            tagged Jmp (tagged JmpC '{.c, .a}) : if (rf[c]) pc = a;
        //          endcase
        //        end"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          case (instr) matches
        //            tagged Add '{reg2:.r2,regd:.rd,reg1:.r1} &&& (rd != 0):
        //                                                     rf[rd] = rf[r1] + rf[r2];
        //            tagged Jmp (tagged JmpU .a) : pc = pc + a;
        //            tagged Jmp (tagged JmpC '{addr:.a,cc:.c}) : if (rf[c]) pc = a;
        //          endcase
        //        end"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          if (e matches (tagged Jmp (tagged JmpC '{cc:.c,addr:.a})))
        //            ; // c and a can be used here
        //          else
        //            ;
        //        end"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          if (e matches (tagged Jmp .j) &&&
        //              j matches (tagged JmpC '{cc:.c,addr:.a}))
        //            ; // c and a can be used here
        //          else
        //            ;
        //        end"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          if (e matches (tagged Jmp (tagged JmpC '{cc:.c,addr:.a}))
        //            &&& (rf[c] != 0))
        //            ; // c and a can be used here
        //          else
        //            ;
        //        end"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"module m;
        //          initial begin
        //            for (int i = 0; i <= 255; i++)
        //          end

        //          initial begin
        //            loop2: for (int i = 15; i >= 0; i--)
        //          end
        //        endmodule"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"module m;
        //          initial begin
        //            begin
        //              automatic int i;
        //              for (i = 0; i <= 255; i++)
        //            end
        //          end

        //          initial begin
        //            begin : loop2
        //              automatic int i;
        //              for (i = 15; i >= 0; i--)
        //            end
        //          end
        //        endmodule"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"initial begin
                  for ( int count = 0; count < 3; count++ )
                    value = value +((a[count]) * (count+1));

                  for ( int count = 0, done = 0, j = 0; j * count < 125; j++, count++)
                    $display("Value j = %d\n", j );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  parameter size = 8, longsize = 16;
                  logic [size:1] opa, opb;
                  logic [longsize:1] result;

                  begin : mult
                    logic [longsize:1] shift_opa, shift_opb;
                    shift_opa = opa;
                    shift_opb = opb;
                    result = 0;
                    repeat (size) begin
                      if (shift_opb[1])
                        result = result + shift_opa;
                      shift_opa = shift_opa << 1;
                      shift_opb = shift_opb >> 1;
                    end
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string words [2] = '{ "hello", "world" };
                  int prod [1:8] [1:3];

                  foreach( words [ j ] )
                    $display( j , words[j] ); // print each index and value

                  foreach( prod[ k, m ] )
                    prod[k][m] = k * m;       // initialize
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  begin : count1s
                    logic [7:0] tempreg;
                    count = 0;
                    tempreg = data;
                    while (tempreg) begin
                      if (tempreg[0])
                        count++;
                      tempreg >>= 1;
                    end
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string s;
                  if ( map.first( s ) )
                    do
                      $display( "%s : %d\n", s, map[ s ] );
                    while ( map.next( s ) );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  clock1 <= 0;
                  clock2 <= 0;
                  fork
                    forever #10 clock1 = ~clock1;
                    #5 forever #10 clock2 = ~clock2;
                  join
                end"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause13() {
        test!(
            many1(module_item),
            r##"initial begin
                  switch_bytes (old_word, new_word);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  new_word = switch_bytes (old_word);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task mytask1 (output int x, input logic y);
                endtask

                task mytask2;
                  output x;
                  input y;
                  int x;
                  logic y;
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task mytask3(a, b, output logic [15:0] u, v);
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task mytask4(input [3:0][7:0] a, b[3:0], output [3:0][7:0] y[1:0]);
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task my_task;
                  input a, b;
                  inout c;
                  output d, e;
                  c = a; // the assignments that initialize result outputs
                  d = b;
                  e = c;
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task my_task (input a, b, inout c, output d, e);
                  c = a; // the assignments that initialize result variables
                  d = b;
                  e = c;
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial
                  my_task (v, w, x, y, z);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  a = v;
                  b = w;
                  c = x;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  x = c;
                  y = d;
                  z = e;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module traffic_lights;
                  logic clock, red, amber, green;
                  parameter on = 1, off = 0, red_tics = 350,
                            amber_tics = 30, green_tics = 200;

                  // initialize colors
                  initial red = off;
                  initial amber = off;
                  initial green = off;

                  always begin                // sequence to control the lights
                    red = on;                 // turn red light on
                    light(red, red_tics);     // and wait.
                    green = on;               // turn green light on
                    light(green, green_tics); // and wait.
                    amber = on;               // turn amber light on
                    light(amber, amber_tics); // and wait.
                  end

                  // task to wait for 'tics' positive edge clocks
                  // before turning 'color' light off
                  task light (output color, input [31:0] tics);
                    repeat (tics) @ (posedge clock);
                    color = off; // turn light off.
                  endtask: light

                  always begin   // waveform for the clock
                    #100 clock = 0;
                    #100 clock = 1;
                  end
                endmodule: traffic_lights"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"function logic [15:0] myfunc1(int x, int y);
                endfunction

                function logic [15:0] myfunc2;
                  input int x;
                  input int y;
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"function logic [15:0] myfunc3(int a, int b, output logic [15:0] u, v);
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"function [3:0][7:0] myfunc4(input [3:0][7:0] a, b[3:0]);
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"function [15:0] myfunc1 (input [7:0] x,y);
                  myfunc1 = x * y - 1; // return value assigned to function name
                endfunction

                function [15:0] myfunc2 (input [7:0] x,y);
                  return x * y - 1; //return value is specified using return statement
                endfunction"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          a = b + myfunc1(c, d); // call myfunc1 (defined above) as an expression

        //          myprint(a);            // call myprint (defined below) as a statement

        //          function void myprint (int a);
        //          endfunction
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"initial begin
                  void'(some_function());
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module tryfact;
                  // define the function
                  function automatic integer factorial (input [31:0] operand);
                    if (operand >= 2)
                      factorial = factorial (operand - 1) * operand;
                    else
                      factorial = 1;
                  endfunction: factorial

                  // test the function
                  integer result;
                  initial begin
                    for (int n = 0; n <= 7; n++) begin
                      result = factorial(n);
                      $display("%0d factorial=%0d", n, result);
                    end
                  end
                endmodule: tryfact"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"module ram_model (address, write, chip_select, data);
        //          parameter data_width = 8;
        //          parameter ram_depth = 256;
        //          localparam addr_width = clogb2(ram_depth);
        //          input [addr_width - 1:0] address;
        //          input write, chip_select;
        //          inout [data_width - 1:0] data;

        //          //define the clogb2 function
        //          function integer clogb2 (input [31:0] value);
        //            value = value - 1;
        //            for (clogb2 = 0; value > 0; clogb2 = clogb2 + 1)
        //              value = value >> 1;
        //          endfunction

        //          logic [data_width - 1:0] data_store[0:ram_depth - 1];
        //            //the rest of the ram model
        //        endmodule: ram_model"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"ram_model #(32,421) ram_a0(a_addr,a_wr,a_cs,a_data);"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"class IntClass;
        //          int a;
        //        endclass

        //        IntClass address=new(), stack=new();

        //        function automatic bit watch_for_zero( IntClass p );
        //          fork
        //            forever @p.a begin
        //              if ( p.a == 0 ) $display (“Unexpected zero”);
        //            end
        //          join_none
        //          return ( p.a == 0 );
        //        endfunction

        //        function bit start_check();
        //          return ( watch_for_zero( address ) | watch_for_zero( stack ) );
        //        endfunction

        //        bit y = watch_for_zero( stack ); // illegal

        //        initial if ( start_check() ) $display ( “OK”); // legal

        //        initial fork
        //          if (start_check() ) $display( “OK too”); // legal
        //        join_none"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"function automatic int crc( byte packet [1000:1] );
                  for( int j= 1; j <= 1000; j++ ) begin
                    crc ^= packet[j];
                  end
                endfunction"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          subroutine( ref type argument );
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"function automatic int crc( ref byte packet [1000:1] );
                  for( int j= 1; j <= 1000; j++ ) begin
                    crc ^= packet[j];
                  end
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  byte packet1[1000:1];
                  int k = crc( packet1 ); // pass by value or by reference: call is the same
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"task automatic incr( ref input int a );// incorrect: ref cannot be qualified"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"task automatic show ( const ref byte data [] );
                  for ( int j = 0; j < data.size ; j++ )
                    $display( data[j] ); // data can be read but not written
                endtask"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"task read(int j = 0, int k, int data = 1 );
        //        endtask"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"initial begin
                  read( , 5 );     // is equivalent to read( 0, 5, 1 );
                  read( 2, 5 );    // is equivalent to read( 2, 5, 1 );
                  read( , 5, );    // is equivalent to read( 0, 5, 1 );
                  read( , 5, 7 );  // is equivalent to read( 0, 5, 7 );
                  read( 1, 5, 2 ); // is equivalent to read( 1, 5, 2 );
                  read( );         // error; k has no default value
                  read( 1, , 7 );  // error; k has no default value
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"module m;
        //          logic a, w;

        //          task t1 (output o = a) ; // default binds to m.a
        //          endtask :t1

        //          task t2 (output o = b) ; // illegal, b cannot be resolved
        //          endtask :t2

        //          task t3 (inout io = w) ; // default binds to m.w
        //          endtask :t1
        //        endmodule :m

        //        module n;
        //          logic a;

        //          initial begin
        //            m.t1(); // same as m.t1(m.a), not m.t1(n.a);
        //                    // at end of task, value of t1.o is copied to m.a
        //            m.t3(); // same as m.t3(m.w)
        //                    // value of m.w is copied to t3.io at start of task and
        //                    // value of t3.io is copied to m.w at end of task
        //          end
        //        endmodule :n"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"function int fun( int j = 1, string s = "no" );
        //        endfunction"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"initial begin
                  fun( .j(2), .s("yes") ); // fun( 2, "yes" );
                  fun( .s("yes") );        // fun( 1, "yes" );
                  fun( , "yes" );          // fun( 1, "yes" );
                  fun( .j(2) );            // fun( 2, "no" );
                  fun( .s("yes"), .j(2) ); // fun( 2, "yes" );
                  fun( .s(), .j() );       // fun( 1, "no" );
                  fun( 2 );                // fun( 2, "no" );
                  fun( );                  // fun( 1, "no" );
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          fun( .s("yes"), 2 ); // illegal
        //          fun( 2, .s("yes") ); // OK
        //        end"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"virtual class C#(parameter DECODE_W, parameter ENCODE_W = $clog2(DECODE_W));
        //          static function logic [ENCODE_W-1:0] ENCODER_f
        //                (input logic [DECODE_W-1:0] DecodeIn);
        //            ENCODER_f = '0;
        //            for (int i=0; i<DECODE_W; i++) begin
        //              if(DecodeIn[i]) begin
        //                ENCODER_f = i[ENCODE_W-1:0];
        //                break;
        //              end
        //            end
        //          endfunction
        //          static function logic [DECODE_W-1:0] DECODER_f
        //                (input logic [ENCODE_W-1:0] EncodeIn);
        //            DECODER_f = '0;
        //            DECODER_f[EncodeIn] = 1'b1;
        //          endfunction
        //        endclass"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"module top ();
        //          logic [7:0] encoder_in;
        //          logic [2:0] encoder_out;
        //          logic [1:0] decoder_in;
        //          logic [3:0] decoder_out;

        //          // Encoder and Decoder Input Assignments
        //          assign encoder_in = 8'b0100_0000;
        //          assign decoder_in = 2'b11;

        //          // Encoder and Decoder Function calls
        //          assign encoder_out = C#(8)::ENCODER_f(encoder_in);
        //          assign decoder_out = C#(4)::DECODER_f(decoder_in);

        //          initial begin
        //            #50;
        //            $display("Encoder input = %b Encoder output = %b\n",
        //              encoder_in, encoder_out );
        //            $display("Decoder input = %b Decoder output = %b\n",
        //              decoder_in, decoder_out );
        //          end
        //        endmodule"##,
        //    Ok((_, _))
        //);
    }

    #[test]
    fn clause14() {
        //test!(
        //    many1(module_item),
        //    r##"clocking ck1 @(posedge clk);
        //          default input #1step output negedge; // legal
        //          // outputs driven on the negedge clk
        //          input ;
        //          output ;
        //        endclocking

        //        clocking ck2 @(clk); // no edge specified!
        //          default input #1step output negedge; // legal
        //          input ;
        //          output ;
        //        endclocking"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"clocking bus @(posedge clock1);
        //          default input #10ns output #2ns;
        //          input data, ready, enable = top.mem1.enable;
        //          output negedge ack;
        //          input #1step addr;
        //        endclocking"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"clocking dram @(clk);
        //          input #1ps address;
        //          input #5 output #6 data;
        //        endclocking"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"clocking cd1 @(posedge phi1);
        //          input #1step state = top.cpu1.state;
        //        endclocking"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"clocking mem @(clock);
                  input instruction = { opcode, regA, regB[3:1] };
                endclocking"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"program test( input phi1, input [15:0] data, output logic write,
        //          input phi2, inout [8:1] cmd, input enable
        //        );
        //          reg [8:1] cmd_reg;

        //          clocking cd1 @(posedge phi1);
        //            input data;
        //            output write;
        //            input state = top.cpu1.state;
        //          endclocking

        //          clocking cd2 @(posedge phi2);
        //            input #2 output #4ps cmd;
        //            input enable;
        //          endclocking

        //          initial begin
        //            // program begins here
        //            // user can access cd1.data , cd2.cmd , etc…
        //          end
        //          assign cmd = enable ? cmd_reg: 'x;
        //        endprogram"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"module top;
                  logic phi1, phi2;
                  wire [8:1] cmd; // cannot be logic (two bidirectional drivers)
                  logic [15:0] data;

                  test main (phi1, data, write, phi2, cmd, enable);
                  cpu cpu1 (phi1, data, write);
                  mem mem1 (phi2, cmd, enable);
                endmodule"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"interface bus_A (input clk);
        //          logic [15:0] data;
        //          logic write;
        //          modport test (input data, output write);
        //          modport dut (output data, input write);
        //        endinterface

        //        interface bus_B (input clk);
        //          logic [8:1] cmd;
        //          logic enable;
        //          modport test (input enable);
        //          modport dut (output enable);
        //        endinterface

        //        program test( bus_A.test a, bus_B.test b );
        //          clocking cd1 @(posedge a.clk);
        //            input data = a.data;
        //            output write = a.write;
        //            inout state = top.cpu1.state;
        //          endclocking

        //          clocking cd2 @(posedge b.clk);
        //            input #2 output #4ps cmd = b.cmd;
        //            input en = b.enable;
        //          endclocking

        //          initial begin
        //            // program begins here
        //            // user can access cd1.data, cd1.write, cd1.state,
        //            // cd2.cmd, and cd2.en
        //          end
        //        endprogram"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"module top;
                  logic phi1, phi2;

                  bus_A a (phi1);
                  bus_B b (phi2);

                  test main (a, b);
                  cpu cpu1 (a);
                  mem mem1 (b);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"clocking dram @(posedge phi1);
                  inout data;
                  output negedge #1 address;
                endclocking"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @(dram);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  ##5;       // wait 5 cycles (clocking events) using the default clocking

                  ##(j + 1); // wait j+1 cycles (clocking events) using the default clocking
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"program test(input logic clk, input logic [15:0] data);
                  default clocking bus @(posedge clk);
                    inout data;
                  endclocking

                  initial begin
                    ## 5;
                    if (bus.data == 10)
                      ## 1;
                  end
                endprogram"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"module processor ...
        //          clocking busA @(posedge clk1); ... endclocking
        //          clocking busB @(negedge clk2); ... endclocking
        //          module cpu( interface y );
        //            default clocking busA ;
        //            initial begin
        //              ## 5; // use busA => (posedge clk1)
        //            end
        //          endmodule
        //        endmodule"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"clocking cb @(negedge clk);
                  input v;
                endclocking

                always @(cb) $display(cb.v);

                always @(negedge clk) $display(cb.v);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  logic clk1, clk2;
                  global clocking sys @(clk1 or clk2); endclocking
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  subsystem1 sub1();
                  subsystem2 sub2();
                endmodule

                module subsystem1;
                  logic subclk1;
                  global clocking sub_sys1 @(subclk1); endclocking
                  common_sub common();
                endmodule

                module subsystem2;
                  logic subclk2;
                  global clocking sub_sys2 @(subclk2); endclocking
                  common_sub common();
                endmodule

                module common_sub;
                  always @($global_clock) begin
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  subsystem1 sub1();
                  subsystem2 sub2();
                endmodule

                module subsystem1;
                  logic subclk1, req, ack;
                  global clocking sub_sys1 @(subclk1); endclocking
                  common_checks checks(req, ack);
                endmodule

                module subsystem2;
                  logic subclk2, req, ack;
                  global clocking sub_sys2 @(subclk2); endclocking
                  common_checks checks(req, ack);
                endmodule

                module another_module;
                  logic another_clk;
                  global clocking another_clocking @(another_clk); endclocking
                  property p(req, ack);
                    @($global_clock) req |=> ack;
                  endproperty
                endmodule

                checker common_checks(logic req, logic ack);
                  assert property (another_module.p(req, ack));
                endchecker"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  subsystem1 sub1();
                  subsystem2 sub2();
                endmodule

                module subsystem1;
                  logic subclk1, req, ack;
                  global clocking sub_sys1 @(subclk1); endclocking
                  always another_module.t(req, ack);
                endmodule

                module subsystem2;
                  logic subclk2, req, ack;
                  global clocking sub_sys2 @(subclk2); endclocking
                  always another_module.t(req, ack);
                endmodule

                module another_module;
                  logic another_clk;
                  global clocking another_clocking @(another_clk); endclocking
                  task t(input req, input ack);
                    @($global_clock);
                  endtask
                endmodule"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"module top;
        //          logic a, b, c, clk;
        //          global clocking top_clocking @(clk); endclocking

        //          property p1(req, ack);
        //            @($global_clock) req |=> ack;
        //          endproperty

        //          property p2(req, ack, interrupt);
        //            @($global_clock) accept_on(interrupt) p1(req, ack);
        //          endproperty

        //          my_checker check(
        //            p2(a, b, c),
        //            @$global_clock a[*1:$] ##1 b);
        //        endmodule

        //        checker my_checker(property p, sequence s);
        //          logic checker_clk;
        //          global clocking checker_clocking @(checker_clk); endclocking
        //          assert property (p);
        //          cover property (s);
        //        endchecker"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"initial begin
                  @(ram_bus.ack_l);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @(ram_bus);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @(posedge ram_bus.enable);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @(negedge dom.sign[a]);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @(posedge dom.sig1 or dom.sig2);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @(negedge dom.sig1 or posedge dom.sig2);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @(edge dom.sig1);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @(negedge dom.sig1 or posedge dom.sig1);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  bus.data[3:0] <= 4'h5; // drive data in Re-NBA region of the current cycle

                  ##1 bus.data <= 8'hz;  // wait 1 default clocking cycle, then drive data

                  ##2; bus.data <= 2;    // wait 2 default clocking cycles, then drive data

                  bus.data <= ##2 r;     // remember the value of r and then drive
                                         // data 2 (bus) cycles later

                  bus.data <= #4 r;      // error: regular intra-assignment delay not allowed
                                         // in synchronous drives
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"default clocking cb @(posedge clk); // Assume clk has a period of #10 units
                  output v;
                endclocking

                initial begin
                  #3 cb.v <= expr1; // Matures in cycle 1; equivalent to ##1 cb.v <= expr1
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"clocking cb @(posedge clk);
                  inout a;
                  output b;
                endclocking

                initial begin
                  cb.a <= c;    // The value of a will change in the Re-NBA region
                  cb.b <= cb.a; // b is assigned the value of a before the change
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"default clocking pe @(posedge clk);
                  output nibble; // four bit output
                endclocking

                initial begin
                  ##2;
                  pe.nibble <= 4'b0101;
                  pe.nibble <= 4'b0011;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m;
                  bit a = 1'b1;
                  default clocking cb @(posedge clk);
                    output a;
                  endclocking

                  initial begin
                    ## 1;
                    cb.a <= 1'b0;
                    @(x); // x is triggered by reactive stimulus running in same time step
                    cb.a <= 1'b1;
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit v;
                default clocking cb @(posedge clk);
                  output v;
                endclocking

                initial begin
                  ##1;                   // Wait until cycle 1
                  cb.v <= expr1;         // Matures in cycle 1, v is assigned expr1
                  cb.v <= ##2 expr2;     // Matures in cycle 3
                  #1 cb.v <= ##2 expr3;  // Matures in cycle 3
                  ##1 cb.v <= ##1 expr4; // Matures in cycle 3, v is assigned expr4
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"reg j;

                clocking pe @(posedge clk);
                  output j;
                endclocking

                clocking ne @(negedge clk);
                  output j;
                endclocking"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"reg j;
                clocking e @(edge clk);
                  output j;
                endclocking"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause15() {
        test!(
            many1(module_item),
            r##"initial begin
                  semaphore smTx;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  mailbox mbxRcv;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  typedef mailbox #(string) s_mbox;

                  s_mbox sm = new;
                  string s;

                  sm.put( "hello" );
                  sm.get( s ); // s <- "hello"
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @ hierarchical_event_identifier;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  wait ( hierarchical_event_identifier.triggered );
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          event done, blast;     // declare two new events
        //          event done_too = done; // declare done_too as alias to done

        //          task trigger( event ev );
        //            -> ev;
        //          endtask

        //          fork
        //            @ done_too;         // wait for done through done_too
        //            #1 trigger( done ); // trigger done through task trigger
        //          join

        //          fork
        //            -> blast;
        //            wait ( blast.triggered );
        //          join
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"initial begin
                  wait_order( a, b, c);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  wait_order( a, b, c ) else $display( "Error: events out of order" );
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          bit success;
        //          wait_order( a, b, c ) success = 1; else success = 0;
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"initial begin
                  event a, b, c;
                  a = b;
                  -> c;
                  -> a; // also triggers b
                  -> b; // also triggers a
                  a = c;
                  b = a;
                  -> a; // also triggers b and c
                  -> b; // also triggers a and c
                  -> c; // also triggers a and b
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork
                    T1: forever @ E2;
                    T2: forever @ E1;
                    T3: begin
                          E2 = E1;
                          forever -> E2;
                    end
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  event E1 = null;
                  @ E1;                 // undefined: might block forever or not at all
                  wait( E1.triggered ); // undefined
                  -> E1;                // no effect
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  event E1, E2;
                  if ( E1 ) // same as if ( E1 != null )
                    E1 = E2;
                  if ( E1 == E2 )
                    $display( "E1 and E2 are the same event" );
                end"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause16() {
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          assert_f: assert(f) $info("passed"); else $error("failed");
        //          assume_inputs: assume (in_a || in_b) $info("assumption holds");
        //          else $error("assumption does not hold");
        //          cover_a_and_b: cover (in_a && in_b) $info("in_a && in_b == 1 covered");<Paste>
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"time t;

                always @(posedge clk)
                  if (state == REQ)
                    assert (req1 || req2)
                    else begin
                      t = $time;
                      #5 $error("assert failed at time %0t",t);
                    end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          assert (myfunc(a,b)) count1 = count + 1; else ->event1;
        //          assert (y == 0) else flag = 1;
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"assign not_a = !a;
                always_comb begin : b1
                  a1: assert (not_a != a);
                  a2: assert #0 (not_a != a); // Should pass once values have settled
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"always @(a or b) begin : b1
        //          a3: assert #0 (a == b) rptobj.success(0); else rptobj.error(0, a, b);
        //          #1;
        //          a4: assert #0 (a == b) rptobj.success(1); else rptobj.error(1, a, b);
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"always_comb begin : b1
                  c1: cover (b != a);
                  c2: cover #0 (b != a);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"function f(bit v);
                  p: assert #0 (v);
                endfunction
                always_comb begin: myblk
                  a = b || f(c);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"function int error_type (int opcode);
                  func_assert: assert (opcode < 64) else $display("Opcode error.");
                  if (opcode < 32)
                    return (0);
                  else
                    return (1);
                endfunction

                always_comb begin : b1
                  a1: assert #0 (my_cond) else
                  $error("Error on operation of type %d\n", error_type(opcode));
                  a2: assert #0 (my_cond) else
                  error_type(opcode);
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"module dut(input logic clk, input logic a, input logic b);
        //          logic c;
        //          always_ff @(posedge clk)
        //            c <= b;
        //          a1: assert #0 (!(a & c)) $display("Pass"); else $display("Fail");
        //          a2: assert final (!(a & c)) $display("Pass"); else $display("Fail");
        //        endmodule

        //        program tb(input logic clk, output logic a, output logic b);
        //          default clocking m @(posedge clk);
        //            default input #0;
        //            default output #0;
        //            output a;
        //            output b;
        //          endclocking

        //          initial begin
        //            a = 1;
        //            b = 0;
        //            ##10;
        //            b = 1;
        //            ##1;
        //            a = 0;
        //          end
        //        endprogram

        //        module sva_svtb;
        //          bit clk;
        //          logic a, b;
        //          dut dut (.*);
        //          tb tb (.*);
        //        endmodule"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"module m (input a, b);
                  a1: assert #0 (a == b);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m (input a, b);
                  always_comb begin
                    a1: assert #0 (a == b);
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(bad_val or bad_val_ok) begin : b1
                  a1: assert #0 (bad_val) else $fatal(1, "Sorry");
                  if (bad_val_ok) begin
                    disable a1;
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(a or b or c) begin : b2
                  if (c == 8'hff) begin
                    a2: assert #0 (a && b);
                  end else begin
                    a3: assert #0 (a || b);
                  end
                end

                always @(clear_b2) begin : b3
                  disable b2;
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"module fsm();
        //          function bit f (int a, int b)
        //            a1: assert #0 (a == b);
        //          endfunction

        //          always_comb begin : b1
        //            some_stuff = f(x,y);
        //          end

        //          always_comb begin : b2
        //            other_stuff = f(z,w);
        //          end
        //        endmodule"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"global clocking @clk; endclocking
        //        assert property(@$global_clock a);"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"assert property(@clk a);"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"base_rule1: assert property (cont_prop(rst,in1,in2)) $display("%m, passing");
        //                     else $display("%m, failed");"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"bit a;
                integer b;
                byte q[$];

                property p1;
                  $rose(a) |-> q[0];
                endproperty

                property p2;
                  integer l_b;
                  ($rose(a), l_b = b) |-> ##[3:10] q[l_b];
                endproperty"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"bit [2:0] count;
        //        realtime t;

        //        initial count = 0;
        //        always @(posedge clk) begin
        //          if (count == 0) t = $realtime; //capture t in a procedural context
        //          count++;
        //        end

        //        property p1;
        //          @(posedge clk)
        //          count == 7 |-> $realtime – t < 50.5;
        //        endproperty

        //        property p2;
        //          realtime l_t;
        //          @(posedge clk)
        //          (count == 0, l_t = $realtime) ##1 (count == 7)[->1] |->
        //            $realtime – l_t < 50.5;
        //        endproperty"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"sequence delay_example(x, y, min, max, delay1);
                  x ##delay1 y[*min:max];
                endsequence

                // Legal
                a1: assert property (@(posedge clk) delay_example(x, y, 3, $, 2));

                int z, d;

                // Illegal: z and d are not elaboration-time constants
                a2_illegal: assert property (@(posedge clk) delay_example(x, y, z, $, d));"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s1;
                  @(posedge clk) a ##1 b ##1 c;
                endsequence
                sequence s2;
                  @(posedge clk) d ##1 e ##1 f;
                endsequence
                sequence s3;
                  @(negedge clk) g ##1 h ##1 i;
                endsequence
                sequence s4;
                  @(edge clk) j ##1 k ##1 l;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s20_1(data,en);
                  (!frame && (data==data_bus)) ##1 (c_be[0:3] == en);
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s;
                  a ##1 b ##1 c;
                endsequence
                sequence rule;
                  @(posedge sysclk)
                  trans ##1 start_trans ##1 s ##1 end_trans;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence rule;
                  @(posedge sysclk)
                  trans ##1 start_trans ##1 (a ##1 b ##1 c) ##1 end_trans ;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s1;
                  @(posedge sysclk) (x ##1 s2);
                endsequence
                sequence s2;
                  @(posedge sysclk) (y ##1 s1);
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s1(w, x, y);
                  w ##1 x ##[2:10] y;
                endsequence
                sequence s2(w, y, bit x);
                  w ##1 x ##[2:10] y;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence delay_arg_example (max, shortint delay1, delay2, min);
                  x ##delay1 y[*min:max] ##delay2 z;
                endsequence

                parameter my_delay=2;
                cover property (delay_arg_example($, my_delay, my_delay-1, 3));"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"cover property (x ##2 y[*3:$] ##1 z);"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"sequence event_arg_example (event ev);
        //          @(ev) x ##1 y;
        //        endsequence

        //        cover property (event_arg_example(posedge clk));"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"cover property (@(posedge clk) x ##1 y));"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"sequence event_arg_example2 (reg sig);
                  @(posedge sig) x ##1 y;
                endsequence

                cover property (event_arg_example2(clk));"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"cover property (@(posedge clk) x ##1 y));"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"sequence s(bit a, bit b);
                  bit loc_a;
                  (1'b1, loc_a = a) ##0
                  (t == loc_a) [*0:$] ##1 b;
                endsequence"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"logic b_d, d_d;
        //        sequence legal_loc_var_formal (
        //          local inout logic a,
        //          local logic b = b_d, // input inferred, default actual argument b_d
        //                      c,       // local input logic inferred, no default
        //                               // actual argument
        //                      d = d_d, // local input logic inferred, default actual
        //                               // argument d_d
        //          logic e, f           // e and f are not local variable formal arguments
        //        );
        //          logic g = c, h = g || d;
        //        endsequence"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"sequence illegal_loc_var_formal (
        //          output logic a,            // illegal: local must be specified with
        //                                     // direction
        //          local inout logic b,
        //                            c = 1'b0,// default actual argument illegal for inout
        //          local d = expr,            // illegal: type must be specified explicitly
        //          local event e,             // illegal: event is a type disallowed in
        //                                     // 16.6
        //          local logic f = g          // g shall not refer to the local variable
        //                                     // below and must be resolved upward from
        //                                     // this declaration
        //        );
        //          logic g = b;
        //        endsequence"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"sequence sub_seq2(local inout int lv);
        //          (a ##1 !a, lv += data_in)
        //          ##1 !b[*0:$] ##1 b && (data_out == lv);
        //        endsequence
        //        sequence seq2;
        //          int v1;
        //          (c, v1 = data)
        //          ##1 sub_seq2(v1) // lv is initialized by assigning it the value of v1;
        //                           // when the instance sub_seq2(v1) matches, v1 is
        //                           // assigned the value of lv
        //          ##1 (do1 == v1);
        //        endsequence"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"sequence seq2_inlined;
                  int v1, lv;
                  (c, v1 = data) ##1
                  (
                    (1, lv = v1) ##0
                    (a ##1 !a, lv += data_in)
                    ##1 (!b[*0:$] ##1 b && (data_out == lv), v1 = lv)
                  )
                  ##1 (do1 == v1);
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic a, b, clk;
                // ...
                a1_bad: assert property (@clk a == b)
                  else $error("Different values: a = %b, b = %b", a, b);
                a2_ok: assert property (@clk a == b)
                  else $error("Different values: a = %b, b = %b",
                    $sampled(a), $sampled(b));"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(posedge clk)
                  reg1 <= a & $rose(b);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  $past(in1, , enable);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(posedge clk)
                  reg1 <= a & $past(b);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(posedge clk)
                  for (int i = 0; i < 4; i ++)
                    if (cond[i])
                      reg1[i] <= $past(b[i]);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(posedge clk)
                  if (enable) q <= d;

                always @(posedge clk)
                assert property (done |=> (out == $past(q, 2,enable)) );"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"bit clk, fclk, req, gnt, en;

        //        a1: assert property
        //          (@(posedge clk) en && $rose(req) |=> gnt);
        //        a2: assert property
        //          (@(posedge clk) en && $rose(req, @(posedge fclk)) |=> gnt);"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"always_ff @(posedge clk1)
        //          reg1 <= $rose(b, @(posedge clk2));"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"always @(posedge clk) begin
                  @(negedge clk2);
                  x = $past(y, 5); // illegal if not within default clocking
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"a1: assert property (@clk $future_gclk(a || $rising_gclk(b));
        //        sequence s;
        //          bit v;
        //          (a, v = a) ##1 (b == v)[->1];
        //        endsequence : s

        //        // Illegal: a global clocking future sampled value function shall not
        //        // be used in an assertion containing sequence match items
        //        a2: assert property (@clk s |=> $future_gclk(c));"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"a1: assert property (@$global_clock $changing_gclk(sig)
        //                                         |-> $falling_gclk(clk))
        //        else $error(”sig is not stable”);"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"a2: assume property(@$global_clock
        //                    $falling_gclk(clk) ##1 (!$falling_gclk(clk)[*1:$]) |->
        //                                                          $steady_gclk(sig));"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"a3: assert property (@$global_clock disable iff (rst) $changing_gclk(sig)
        //                                             |-> $falling_gclk(clk))
        //        else $error(”sig is not stable”);"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"a4: assert property (##1 $stable_gclk(sig));
                // In a5, there is no issue at cycle 0
                a5: assert property ($steady_gclk(sig));"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence t1;
                  te1 ## [2:5] te2;
                endsequence
                sequence ts1;
                  first_match(te1 ## [2:5] te2);
                endsequence"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"sequence t2;
        //          (a ##[2:3] b) or (c ##[1:2] d);
        //        endsequence
        //        sequence ts2;
        //          first_match(t2);
        //        endsequence"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"sequence burst_rule1;
        //          @(posedge mclk)
        //            $fell(burst_mode) ##0
        //            ((!burst_mode) throughout (##2 ((trdy==0)&&(irdy==0)) [*7]));
        //        endsequence"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"sequence s;
                  a ##1 b ##1 c;
                endsequence
                sequence rule;
                  @(posedge sysclk)
                    trans ##1 start_trans ##1 s ##1 end_trans;
                endsequence"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"sequence e1;
        //          @(posedge sysclk) $rose(ready) ##1 proc1 ##1 proc2 ;
        //        endsequence
        //        sequence rule;
        //          @(posedge sysclk) reset ##1 inst ##1 e1.triggered ##1 branch_back;
        //        endsequence"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"sequence e2(a,b,c);
        //          @(posedge sysclk) $rose(a) ##1 b ##1 c;
        //        endsequence
        //        sequence rule2;
        //          @(posedge sysclk) reset ##1 inst ##1 e2(ready,proc1,proc2).triggered
        //            ##1 branch_back;
        //        endsequence"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"sequence e2_instantiated;
                  e2(ready,proc1,proc2);
                endsequence
                sequence rule2a;
                  @(posedge sysclk) reset ##1 inst ##1 e2_instantiated.triggered ##1
                branch_back;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence e3(sequence a, untyped b);
                  @(posedge sysclk) a.triggered ##1 b;
                endsequence

                sequence rule3;
                  @(posedge sysclk) reset ##1 e3(ready ##1 proc1, proc2) ##1 branch_back;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence zero_or_one_req;
                  (req==1'b1)[*0:1];
                endsequence"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"sequence s;
        //          logic u, v = a, w = v || b;
        //        endsequence"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"property e;
                  int x;
                  (valid_in, x = pipe_in) |-> ##5 (pipe_out1 == (x+1));
                endproperty"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"sequence data_check;
        //          int x;
        //          a ##1 (!a, x = data_in) ##1 !b[*0:$] ##1 b && (data_out == x);
        //        endsequence
        //        property data_check_p
        //          int x;
        //          a ##1 (!a, x = data_in) |=> !b[*0:$] ##1 b && (data_out == x);
        //        endproperty"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"sequence rep_v;
                  int x = 0;
                  (a[->1], x += data)[*4] ##1 b ##1 c && (data_out == x);
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence count_a_cycles;
                  int x;
                  ($rose(a), x = 1)
                  ##1 (a, x++)[*0:$]
                  ##1 !a && (x <= MAX);
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence sub_seq1;
                  int v1;
                  (a ##1 !a, v1 = data_in) ##1 !b[*0:$] ##1 b && (data_out == v1);
                endsequence
                sequence seq1;
                  c ##1 sub_seq1 ##1 (do1 == v1); // error because v1 is not visible
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence sub_seq2(lv);
                  (a ##1 !a, lv = data_in) ##1 !b[*0:$] ##1 b && (data_out == lv);
                endsequence
                sequence seq2;
                  int v1;
                  c ##1 sub_seq2(v1) // v1 is bound to lv
                  ##1 (do1 == v1);   // v1 holds the value that was assigned to lv
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence seq2a;
                  int v1; c ##1 sub_seq2(v1).triggered ##1 (do1 == v1);
                  // v1 is now bound to lv
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence seq2b;
                  int v1; c ##1 !sub_seq2(v1).triggered ##1 (do1 == v1); // v1 unassigned
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence sub_seq3(lv);
                  int lv; // illegal because lv is a formal argument
                  (a ##1 !a, lv = data_in) ##1 !b[*0:$] ##1 b && (data_out == lv);
                endsequence"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"sequence s4;
        //          int x;
        //          (a ##1 (b, x = data) ##1 c) or (d ##1 (e==x)); // illegal
        //        endsequence"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"sequence s5;
        //          int x,y;
        //          ((a ##1 (b, x = data, y = data1) ##1 c)
        //            or (d ##1 (`true, x = data) ##0 (e==x))) ##1 (y==data2);
        //          // illegal because y is not in the intersection
        //        endsequence
        //        sequence s6;
        //          int x,y;
        //          ((a ##1 (b, x = data, y = data1) ##1 c)
        //            or (d ##1 (`true, x = data) ##0 (e==x))) ##1 (x==data2);
        //          // legal because x is in the intersection
        //        endsequence"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"sequence s7;
        //          int x,y;
        //          ((a ##1 (b, x = data, y = data1) ##1 c)
        //            and (d ##1 (`true, x = data) ##0 (e==x))) ##1 (x==data2);
        //          // illegal because x is common to both threads
        //        endsequence
        //        sequence s8;
        //          int x,y;
        //          ((a ##1 (b, x = data, y = data1) ##1 c)
        //            and (d ##1 (`true, x = data) ##0 (e==x))) ##1 (y==data2);
        //          // legal because y is in the difference
        //        endsequence"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"sequence s1;
                  logic v, w;
                  (a, v = e) ##1
                  (b[->1], w = f, $display("b after a with v = %h, w = %h\n", v, w));
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p3;
                  b ##1 c;
                endproperty

                c1: cover property (@(posedge clk) a #-# p3);
                a1: assert property (@(posedge clk) a |-> p3);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"a1: assert property (@clk not a ##1 b);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"a2: assert property (@clk not strong(a ##1 b));"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"let ready_exp = (irdy == 0) && ($fell(trdy) || $fell(stop));
                property data_end;
                  @(posedge mclk)
                  $rose(data_phase) |-> ##[1:5] ready_exp;
                endproperty
                a1: assert property(data_end);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"let data_end_exp = data_phase && ready_exp;
                property data_end_rule1;
                  @(posedge mclk)
                  data_end_exp |-> ##[1:2] $rose(frame) ##1 $rose(irdy);
                endproperty
                a2: assert property(data_end_rule1);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property data_end_rule2;
                  @(posedge mclk) ##[1:2] $rose(frame) ##1 $rose(irdy);
                endproperty
                a3: assert property(data_end_rule2);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property write_to_addr;
                  (write_en & data_valid) ##0
                  (write_en && (retire_address[0:4]==addr)) [*2] |->
                  ##[3:8] write_en && !data_valid &&(write_address[0:4]==addr);
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property write_to_addr_nested;
                  (write_en & data_valid) |->
                    (write_en && (retire_address[0:4]==addr)) [*2] |->
                      ##[3:8] write_en && !data_valid && (write_address[0:4]==addr);
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p1;
                  ##[0:5] done #-# always !rst;
                endproperty

                property p2;
                  ##[0:5] done #=# always !rst;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p1;
                  nexttime a;
                endproperty

                // the clock shall tick once more and a shall be true at the next clock tick.
                property p2;
                  s_nexttime a;
                endproperty

                // as long as the clock ticks, a shall be true at each future clock tick
                // starting from the next clock tick
                property p3;
                  nexttime always a;
                endproperty

                // the clock shall tick at least once more and as long as it ticks, a shall
                // be true at every clock tick starting from the next one
                property p4;
                  s_nexttime always a;
                endproperty

                // if the clock ticks at least once more, it shall tick enough times for a to
                // be true at some point in the future starting from the next clock tick
                property p5;
                  nexttime s_eventually a;
                endproperty

                // a shall be true sometime in the strict future
                property p6;
                  s_nexttime s_eventually a;
                endproperty

                // if there are at least two more clock ticks, a shall be true at the second
                // future clock tick
                property p7;
                  nexttime[2] a;
                endproperty

                // there shall be at least two more clock ticks, and a shall be true at the
                // second future clock tick
                property p8;
                  s_nexttime[2] a;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"implicit_always: assert property(p);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial explicit_always: assert property(always p);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial a1: assume property( @(posedge clk) reset[*5] #=# always !reset);

                property p1;
                  a ##1 b |=> always c;
                endproperty

                property p2;
                  always [2:5] a;
                endproperty

                property p3;
                  s_always [2:5] a;
                endproperty

                property p4;
                  always [2:$] a;
                endproperty

                property p5;
                  s_always [2:$] a; // Illegal
                endproperty"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"property p1;
        //          a until b;
        //        endproperty

        //        property p2;
        //          a s_until b;
        //        endproperty

        //        property p3;
        //          a until_with b;
        //        endproperty

        //        property p4;
        //          a s_until_with b;
        //        endproperty"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"property p1;
        //          s_eventually a;
        //        endproperty

        //        property p2;
        //          s_eventually always a;
        //        endproperty

        //        property p3;
        //          always s_eventually a;
        //        endproperty

        //        property p4;
        //          eventually [2:5] a;
        //        endproperty

        //        property p5;
        //          s_eventually [2:5] a;
        //        endproperty

        //        property p6;
        //          eventually [2:$] a; // Illegal
        //        endproperty

        //        property p7;
        //          s_eventually [2:$] a;
        //        endproperty"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"assert property (@(clk) go ##1 get[*2] |-> reject_on(stop) put[->2]);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"assert property (@(clk) go ##1 get[*2] |-> sync_reject_on(stop) put[->2]);"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"assert property (@(clk) go ##1 get[*2] |-> !stop throughout put[->2]);"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"property p; (accept_on(a) p1) and (reject_on(b) p2); endproperty"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"property p; (accept_on(a) p1) or (reject_on(b) p2); endproperty"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"property p; not (accept_on(a) p1); endproperty"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"property p; accept_on(a) reject_on(b) p1; endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p_delay(logic [1:0] delay);
                  case (delay)
                    2'd0 : a && b;
                    2'd1 : a ##2 b;
                    2'd2 : a ##4 b;
                    2'd3 : a ##8 b;
                    default: 0; // cause a failure if delay has x or z values
                  endcase
                endproperty"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"property prop_always(p);
        //          p and (1'b1 |=> prop_always(p));
        //        endproperty"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"property p1(s,p);
                  s |=> prop_always(p);
                endproperty"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"property prop_weak_until(p,q);
        //          q or (p and (1'b1 |=> prop_weak_until(p,q)));
        //        endproperty"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"property p2(s,p,q);
                  s |=> prop_weak_until(p,q);
                endproperty"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"property check_phase1;
        //          s1 |-> (phase1_prop and (1'b1 |=> check_phase2));
        //        endproperty
        //        property check_phase2;
        //          s2 |-> (phase2_prop and (1'b1 |=> check_phase1));
        //        endproperty"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"property illegal_recursion_1(p);
        //          not prop_always(not p);
        //        endproperty

        //        property illegal_recursion_2(p);
        //          p and (1'b1 |=> not illegal_recursion_2(p));
        //        endproperty"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"property illegal_recursion_3(p);
        //          disable iff (b)
        //          p and (1'b1 |=> illegal_recursion_3(p));
        //        endproperty"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"property legal_3(p);
                  disable iff (b) prop_always(p);
                endproperty"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"property illegal_recursion_4(p);
        //          p and (1'b1 |-> illegal_recursion_4(p));
        //        endproperty"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"property fibonacci1 (local input int a, b, n, int fib_sig);
        //          (n > 0)
        //          |->
        //          (
        //            (fib_sig == a)
        //            and
        //            (1'b1 |=> fibonacci1(b, a + b, n - 1, fib_sig))
        //          );
        //        endproperty"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"property fibonacci2 (int a, b, n, fib_sig);
        //          (n > 0)
        //          |->
        //          (
        //            (fib_sig == a)
        //            and
        //            (1'b1 |=> fibonacci2(b, a + b, n - 1, fib_sig))
        //          );
        //        endproperty"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"property p3(p, bit b, abort);
        //          (p and (1'b1 |=> p4(p, b, abort)));
        //        endproperty

        //        property p4(p, bit b, abort);
        //          accept_on(b) reject_on(abort) p3(p, b, abort);
        //        endproperty"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"property check_write;
        //          logic [0:127] expected_data; // local variable to sample model data
        //          logic [3:0] tag; // local variable to sample tag

        //          disable iff (reset)
        //          (
        //            write_request && write_request_ack,
        //            expected_data = model_data,
        //            tag = write_request_ack_tag
        //          )
        //          |=>
        //          check_write_data_beat(expected_data, tag, 4'h0);
        //        endproperty

        //        property check_write_data_beat
        //        (
        //          local input logic [0:127] expected_data,
        //          local input logic [3:0] tag, i
        //        );
        //          (
        //            (data_valid && (data_valid_tag == tag))
        //            ||
        //            (retry && (retry_tag == tag))
        //          )[->1]
        //          |->
        //          (
        //            (
        //              (data_valid && (data_valid_tag == tag))
        //              |->
        //              (data == expected_data[i*8+:8])
        //            )
        //            and
        //            (
        //              if (retry && (retry_tag == tag))
        //              (
        //                1'b1 |=> check_write_data_beat(expected_data, tag, 4'h0)
        //              )
        //              else if (!last_data_valid)
        //              (
        //                1'b1 |=> check_write_data_beat(expected_data, tag, i+4'h1)
        //              )
        //              else
        //              (
        //                ##1 (retry && (retry_tag == tag))
        //                |=>
        //                check_write_data_beat(expected_data, tag, 4'h0)
        //              )
        //            )
        //          );
        //        endproperty"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"property rule1;
                  @(posedge clk) a |-> b ##1 c ##1 d;
                endproperty
                property rule2;
                  @(clkev) disable iff (e) a |-> not(b ##1 c ##1 d);
                endproperty"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"property rule3;
        //          @(posedge clk) a[*2] |-> ((##[1:3] c) or (d |=> e));
        //        endproperty"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"property rule4;
        //          @(posedge clk) a[*2] |-> ((##[1:3] c) and (d |=> e));
        //        endproperty"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"property rule5;
        //          @(posedge clk)
        //          a ##1 (b || c)[->1] |->
        //            if (b)
        //              (##1 d |-> e)
        //            else // c
        //              f ;
        //        endproperty"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"property rule6(x,y);
                  ##1 x |-> y;
                endproperty
                property rule5a;
                  @(posedge clk)
                  a ##1 (b || c)[->1] |->
                    if (b)
                      rule6(d,e)
                    else // c
                      f ;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s1;
                  a ##1 b; // unclocked sequence
                endsequence
                sequence s2;
                  c ##1 d; // unclocked sequence
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence mult_s;
                  @(posedge clk) a ##1 @(posedge clk1) s1 ##1 @(posedge clk2) s2;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property mult_p1;
                  @(posedge clk) a ##1 @(posedge clk1) s1 ##1 @(posedge clk2) s2;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property mult_p2;
                  mult_s;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property mult_p3;
                  @(posedge clk) a ##1 @(posedge clk1) s1 |=> @(posedge clk2) s2;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property mult_p6;
                  mult_s |=> mult_s;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property mult_p7;
                  @(posedge clk) a ##1 b |-> c ##1 @(posedge clk1) d;
                endproperty"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"property mult_p8;
        //          @(posedge clk) a ##1 b |->
        //          if (c)
        //            (1 |=> @(posedge clk1) d)
        //          else
        //            e ##1 @(posedge clk2) f ;
        //        endproperty"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"sequence e1(a,b,c);
        //          @(posedge clk) $rose(a) ##1 b ##1 c ;
        //        endsequence
        //        sequence e2;
        //          @(posedge sysclk) reset ##1 inst ##1 e1(ready,proc1,proc2).matched [->1]
        //            ##1 branch_back;
        //        endsequence"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"sequence e1;
        //          @(posedge sysclk) $rose(a) ##1 b ##1 c;
        //        endsequence

        //        sequence e2;
        //          @(posedge sysclk) reset ##1 inst ##1 e1.triggered ##1 branch_back;
        //        endsequence

        //        sequence e3;
        //          @(posedge clk) reset1 ##1 e1.matched ##1 branch_back1;
        //        endsequence

        //        sequence e2_with_arg(sequence subseq);
        //          @(posedge sysclk) reset ##1 inst ##1 subseq.triggered ##1 branch_back;
        //        endsequence

        //        sequence e4;
        //          e2_with_arg(@(posedge sysclk) $rose(a) ##1 b ##1 c);
        //        endsequence

        //        program check;
        //          initial begin
        //            wait (e1.triggered || e2.triggered);
        //            if (e1.triggered)
        //              $display("e1 passed");
        //            if (e2.triggered)
        //              $display("e2 passed");
        //          end
        //        endprogram"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"module mod_sva_checks;
                  logic a, b, c, d;
                  logic clk_a, clk_d, clk_e1, clk_e2;
                  logic clk_c, clk_p;

                  clocking cb_prog @(posedge clk_p); endclocking
                  clocking cb_checker @(posedge clk_c); endclocking

                  default clocking cb @(posedge clk_d); endclocking

                  sequence e4;
                    $rose(b) ##1 c;
                  endsequence

                  // e4 infers posedge clk_a as per clock flow rules
                  a1: assert property (@(posedge clk_a) a |=> e4.triggered);

                  sequence e5;
                    // e4 will infer posedge clk_e1 as per clock flow rules
                    // wherever e5 is instantiated (with/without a method)
                    @(posedge clk_e1) a ##[1:3] e4.triggered ##1 c;
                  endsequence

                  // e4, used in e5, infers posedge clk_e1 from e5
                  a2: assert property (@(posedge clk_a) a |=> e5.matched);

                  sequence e6(f);
                    @(posedge clk_e2) f;
                  endsequence

                  // e4 infers posedge clk_e2 as per clock flow rules
                  a3: assert property (@(posedge clk_a) a |=> e6(e4.triggered));

                  sequence e7;
                    e4 ##1 e6(d);
                  endsequence

                  // Leading clock of e7 is posedge clk_a as per clock flow rules
                  a4: assert property (@(posedge clk_a) a |=> e7.triggered);

                  // Illegal use in a disable condition, e4 is not explicitly clocked
                  a5_illegal: assert property (
                    @(posedge clk_a) disable iff (e4.triggered) a |=> b);

                  always @(posedge clk_a) begin
                    // e4 infers default clocking cb and not posedge clk_a as there is
                    // more than one event control in this procedure (16.14.6)
                    @(e4);
                    d = a;
                  end

                  program prog_e4;
                    default clocking cb_prog;
                    initial begin
                      // e4 infers default clocking cb_prog
                      wait (e4.triggered);
                      $display("e4 passed");
                    end
                  endprogram : prog_e4

                  checker check(input in1, input sequence s_f);
                    default clocking cb_checker;
                    always @(s_f)
                      $display("sequence triggered");
                    a4: assert property (a |=> in1);
                  endchecker : check

                  // e4 infers checker's default clocking cb_checker
                  check c1(e4.triggered, e4);

                  // e4 connected to port of a module instance infers default clocking cb
                  mod_adder ai1(e4.triggered);

                endmodule : mod_sva_checks"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"property p;
        //          logic v = e;
        //          (@(posedge clk1) (a == v)[*1:$] |-> b)
        //          and
        //          (@(posedge clk2) c[*1:$] |-> d == v)
        //          ;
        //        endproperty
        //        a1: assert property (@(posedge clk) f |=> p);"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"property p;
        //          logic v;
        //          (@(posedge clk1) (1, v = e) ##0 (a == v)[*1:$] |-> b)
        //          and
        //          (@(posedge clk2) (1, v = e) ##0 c[*1:$] |-> d == v)
        //          ;
        //        endproperty"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"property abc(a, b, c);
        //          disable iff (a==2) @(posedge clk) not (b ##1 c);
        //        endproperty
        //        env_prop: assert property (abc(rst, in1, in2))
        //          $display("env_prop passed."); else $display("env_prop failed.");"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"property abc(a, b, c);
        //          disable iff (c) @(posedge clk) a |=> b;
        //        endproperty
        //        env_prop:
        //          assume property (abc(req, gnt, rst)) else $error(”Assumption failed.”);"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"a1:assume property ( @(posedge clk) req dist {0:=40, 1:=60} ) ;
                property proto ;
                  @(posedge clk) req |-> req[*1:$] ##0 ack;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"a1_assertion:assert property ( @(posedge clk) req inside {0, 1} ) ;
                property proto_assertion ;
                  @(posedge clk) req |-> req[*1:$] ##0 ack;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property pr1;
                  @(posedge clk) !reset_n |-> !req; // when reset_n is asserted (0),
                                                    // keep req 0
                endproperty
                property pr2;
                  @(posedge clk) ack |=> !req; // one cycle after ack, req
                                               // must be deasserted
                endproperty
                property pr3;
                  @(posedge clk) req |-> req[*1:$] ##0 ack; // hold req asserted until
                                                            // and including ack asserted
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property pa1;
                  @(posedge clk) !reset_n || !req |-> !ack;
                endproperty
                property pa2;
                  @(posedge clk) ack |=> !ack;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"a1:assume property (@(posedge clk) req dist {0:=40, 1:=60} );
                assume_req1:assume property (pr1);
                assume_req2:assume property (pr2);
                assume_req3:assume property (pr3);

                assert_ack1:assert property (pa1)
                  else $error("ack asserted while req is still deasserted");
                assert_ack2:assert property (pa2)
                  else $error("ack is extended over more than one cycle");"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"restrict property (@(posedge clk) ctr == '0);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top(input logic clk);
                  logic a,b,c;
                  property rule3;
                    @(posedge clk) a |-> b ##1 c;
                  endproperty
                  a1: assert property (rule3);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top(input logic clk);
                  logic a,b,c;
                  sequence seq3;
                    @(posedge clk) b ##1 c;
                  endsequence
                  c1: cover property (seq3);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property rule;
                  a ##1 b ##1 c;
                endproperty
                always @(posedge clk) begin
                  assert property (rule);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property r1;
                  q != d;
                endproperty
                always @(posedge mclk) begin
                  q <= d1;
                  r1_p1: assert property (r1);
                  r1_p2: assert property (@(posedge scanclk)r1);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property r2;
                  q != d;
                endproperty
                always_ff @(posedge clock iff reset == 0 or posedge reset) begin
                  cnt <= reset ? 0 : cnt + 1;
                  q <= $past(d1);
                  r2_p: assert property (r2);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property r3;
                  q != d;
                endproperty
                always_ff @(clock iff reset == 0 or posedge reset) begin
                  cnt <= reset ? 0 : cnt + 1;
                  q <= $past(d1); // no inferred clock
                  r3_p: assert property (r3); // no inferred clock
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property r4;
                  q != d;
                endproperty
                always @(posedge mclk) begin
                  #10 q <= d1; // delay prevents clock inference
                  @(negedge mclk) // event control prevents clock inference
                  #10 q1 <= !d1;
                  r4_p: assert property (r4); // no inferred clock
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(posedge clk) begin
                  int i = 10;
                  for (i=0; i<10; i++) begin
                    a1: assert property (foo[i] && bar[i]);
                    a2: assert property (foo[const'(i)] && bar[i]);
                    a3: assert property (foo[const'(i)] && bar[const'(i)]);
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"default clocking @(posedge clk); endclocking
                generate for (genvar i=0; i<10; i++) begin
                  a1: assert property (foo[10] && bar[10]);
                  a2: assert property (foo[i] && bar[10]);
                  a3: assert property (foo[i] && bar[i]);
                end
                endgenerate"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(posedge clk) begin
                  // variable declared in for statement is automatic (see 12.7.1)
                  for (int i=0; i<10; i++) begin
                    a4: assert property (foo[i] && bar[i]);
                    a5: assert property (foo[const'(i)] && bar[i]);
                    a6: assert property (foo[const'(i)] && bar[const'(i)]);
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"wire w;
                always @(posedge clk) begin : procedural_block_1
                  if (my_activation_condition == 1) begin
                    for (int i=0; i<2; i++) begin
                      a7: assume property (foo[i] |=> bar[i] ##1 (w==1'b1));
                    end
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(posedge clk) begin
                  int i = 10;
                  for (i=0; i<10; i++) begin
                    a8: assert property (foo[const'(i)] && bar[i]) else
                      $error("a8 failed for const i=%d and i=%d",
                        const'(i), $sampled(i));
                  end
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"always @(posedge clk) begin
        //          if (en) begin
        //            a9: assert property p1(a,b,c);
        //          end
        //          if ($sampled(en)) begin
        //            a10: assert property p1(a,b,c);
        //          end
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"assign not_a = !a;
                default clocking @(posedge clk); endclocking
                always_comb begin : b1
                  // Probably better to not use consts in this example
                  // ...but using them to illustrate effects of flushing method
                  a1: assert property (const'(not_a) != const'(a));
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"default clocking @(posedge clk); endclocking
        //        always @(a or b) begin : b1
        //          a2: assert property (a == b) r.success(0) else r.error(0, a, b);
        //          #1;
        //          a3: assert property (a == b) r.success(1) else r.error(1, a, b);
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"default clocking @(posedge clk); endclocking
                always_comb begin : b1
                  c1: cover property (const'(b) != const'(a));
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always_comb begin : procedural_block_1
                  if (en)
                    foo = bar;
                  end

                always_comb begin : procedural_block_2
                  p1: assert property ( @(posedge clk) (const'(foo) == const'(bar)) );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"default clocking @(posedge clk); endclocking
                always @(bad_val or bad_val_ok) begin : b1
                  a1: assert property (bad_val) else $fatal(1, "Sorry");
                  if (bad_val_ok) begin
                    disable a1;
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"default clocking @(posedge clk); endclocking
                always @(a or b or c) begin : b2
                  if (c == 8'hff) begin
                    a2: assert property (a && b);
                  end else begin
                    a3: assert property (a || b);
                  end
                end

                always @(clear_b2) begin : b3
                  disable b2;
                end"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"module m(logic a, b, c, d, rst1, clk1, clk2);
        //          logic rst;

        //          default clocking @(negedge clk1); endclocking
        //          default disable iff rst1;

        //          property p_triggers(start_event, end_event, form, clk = $inferred_clock,
        //                              rst = $inferred_disable);
        //            @clk disable iff (rst)
        //              (start_event ##0 end_event[->1]) |=> form;
        //          endproperty

        //          property p_multiclock(clkw, clkx = $inferred_clock, clky, w, x, y, z);
        //            @clkw w ##1 @clkx x |=> @clky y ##1 z;
        //          endproperty

        //          a1: assert property (p_triggers(a, b, c));
        //          a2: assert property (p_triggers(a, b, c, posedge clk1, 1'b0) );

        //          always @(posedge clk2 or posedge rst) begin
        //          end

        //          a4: assert property(p_multiclock(negedge clk2, , posedge clk1,
        //                              a, b, c, d) );
        //        endmodule"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"module m(logic a, b, c, d, rst1, clk1, clk2);
                  logic rst;

                  a1: assert property (@(negedge clk1) disable iff (rst1)
                                       a ##0 b[->1] |=> c);

                  a2: assert property (@(posedge clk1) disable iff (1'b0)
                                       a ##0 b[->1] |=> c);

                  always @(posedge clk2 or posedge rst) begin
                  end

                  a3: assert property
                    (
                      @(posedge clk2) disable iff (rst1)
                      (a ##0 b[->1]) |=> c
                    );

                  a4: assert property (@(negedge clk2) a ##1 @(negedge clk1) b |=>
                    @(posedge clk1) c ##1 d);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m1;
                  bit clk, rst1;
                  default disable iff rst1;
                  a1: assert property (@(posedge clk) p1); // property p1 is
                                                           // defined elsewhere
                  module m2;
                    bit rst2;
                    a2: assert property (@(posedge clk) p2); // property p2 is
                                                             // defined elsewhere
                  endmodule
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m1;
                  bit clk, rst1;
                  default disable iff rst1;
                  a1: assert property (@(posedge clk) p1); // property p1 is
                                                           // defined elsewhere
                  module m2;
                    bit rst2;
                    default disable iff rst2;
                    a2: assert property (@(posedge clk) p2); // property p2 is
                                                             // defined elsewhere
                  endmodule
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module examples_with_default (input logic a, b, clk, rst, rst1);
                  default disable iff rst;
                  property p1;
                    disable iff (rst1) a |=> b;
                  endproperty

                  // Disable condition is rst1 - explicitly specified within a1
                  a1 : assert property (@(posedge clk) disable iff (rst1) a |=> b);

                  // Disable condition is rst1 - explicitly specified within p1
                  a2 : assert property (@(posedge clk) p1);

                  // Disable condition is rst - no explicit specification, inferred from
                  // default disable iff declaration
                  a3 : assert property (@(posedge clk) a |=> b);

                  // Disable condition is 1'b0. This is the only way to
                  // cancel the effect of default disable.
                  a4 : assert property (@(posedge clk) disable iff (1'b0) a |=> b);
                endmodule

                module examples_without_default (input logic a, b, clk, rst);
                  property p2;
                    disable iff (rst) a |=> b;
                  endproperty

                  // Disable condition is rst - explicitly specified within a5
                  a5 : assert property (@(posedge clk) disable iff (rst) a |=> b);

                  // Disable condition is rst - explicitly specified within p2
                  a6 : assert property (@ (posedge clk) p2);

                  // No disable condition
                  a7 : assert property (@ (posedge clk) a |=> b);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s2; @(posedge clk) a ##2 b; endsequence
                property p2; not s2; endproperty
                assert property (p2);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p3; @(posedge clk) not (a ##2 b); endproperty
                assert property (p3);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(posedge clk) assert property (not (a ##2 b));"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"clocking master_clk @(posedge clk);
                  property p3; not (a ##2 b); endproperty
                endclocking
                assert property (master_clk.p3);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"default clocking master_clk ; // master clock as defined above
                property p4; (a ##2 b); endproperty
                assert property (p4);"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"module examples_with_default (input logic a, b, c, clk);
        //          property q1;
        //            $rose(a) |-> ##[1:5] b;
        //          endproperty

        //          property q2;
        //            @(posedge clk) q1;
        //          endproperty

        //          default clocking posedge_clk @(posedge clk);
        //            property q3;
        //              $fell(c) |=> q1;
        //              // legal: q1 has no clocking event
        //            endproperty

        //            property q4;
        //              $fell(c) |=> q2;
        //              // legal: q2 has clocking event identical to that of
        //              // the clocking block
        //            endproperty

        //            sequence s1;
        //              @(posedge clk) b[*3];
        //              // illegal: explicit clocking event in clocking block
        //            endsequence
        //          endclocking

        //          property q5;
        //            @(negedge clk) b[*3] |=> !b;
        //          endproperty

        //          always @(negedge clk)
        //          begin
        //            a1: assert property ($fell(c) |=> q1);
        //              // legal: contextually inferred leading clocking event,
        //              // @(negedge clk)
        //            a2: assert property (posedge_clk.q4);
        //              // legal: will be queued (pending) on negedge clk, then
        //              // (if matured) checked at next posedge clk (see 16.14.6)
        //            a3: assert property ($fell(c) |=> q2);
        //              // illegal: multiclocked property with contextually
        //              // inferred leading clocking event
        //            a4: assert property (q5);
        //              // legal: contextually inferred leading clocking event,
        //              // @(negedge clk)
        //          end

        //          property q6;
        //            q1 and q5;
        //          endproperty

        //          a5: assert property (q6);
        //            // illegal: default leading clocking event, @(posedge clk),
        //            // but semantic leading clock is not unique
        //          a6: assert property ($fell(c) |=> q6);
        //            // legal: default leading clocking event, @(posedge clk),
        //            // is the unique semantic leading clock

        //          sequence s2;
        //            $rose(a) ##[1:5] b;
        //          endsequence

        //          c1: cover property (s2);
        //            // legal: default leading clocking event, @(posedge clk)
        //          c2: cover property (@(negedge clk) s2);
        //            // legal: explicit leading clocking event, @(negedge clk)
        //        endmodule

        //        module examples_without_default (input logic a, b, c, clk);
        //          property q1;
        //            $rose(a) |-> ##[1:5] b;
        //          endproperty

        //          property q5;
        //            @(negedge clk) b[*3] |=> !b;
        //          endproperty

        //          property q6;
        //            q1 and q5;
        //          endproperty

        //          a5: assert property (q6);
        //            // illegal: no leading clocking event
        //          a6: assert property ($fell(c) |=> q6);
        //            // illegal: no leading clocking event

        //          sequence s2;
        //            $rose(a) ##[1:5] b;
        //          endsequence

        //          c1: cover property (s2);
        //            // illegal: no leading clocking event
        //          c2: cover property (@(negedge clk) s2);
        //            // legal: explicit leading clocking event, @(negedge clk)

        //          sequence s3;
        //            @(negedge clk) s2;
        //          endsequence

        //          c3: cover property (s3);
        //            // legal: leading clocking event, @(negedge clk),
        //            // determined from declaration of s3
        //          c4: cover property (s3 ##1 b);
        //            // illegal: no default, inferred, or explicit leading
        //            // clocking event and maximal property is not an instance
        //        endmodule"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"wire clk1, clk2;
        //        logic a, b;
        //        assign clk2 = clk1;
        //        a1: assert property (@(clk1) a and @(clk2) b); // Illegal
        //        a2: assert property (@(clk1) a and @(clk1) b); // OK
        //        always @(posedge clk1) begin
        //          a3: assert property(a and @(posedge clk2)); //Illegal
        //          a4: assert property(a and @(posedge clk1)); // OK
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"program tst;
                  initial begin
                    # 200ms;
                    expect( @(posedge clk) a ##1 b ##1 c ) else $error( "expect failed" );
                  end
                endprogram"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"integer data;
        //        task automatic wait_for( integer value, output bit success );
        //        expect( @(posedge clk) ##[1:10] data == value ) success = 1;
        //          else success = 0;
        //        endtask

        //        initial begin
        //          bit ok;
        //          wait_for( 23, ok ); // wait for the value 23
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"module A;
                  logic a, clk;

                  clocking cb_with_input @(posedge clk);
                    input a;
                    property p1;
                      a;
                    endproperty
                  endclocking

                  clocking cb_without_input @(posedge clk);
                    property p1;
                      a;
                    endproperty
                  endclocking

                  property p1;
                    @(posedge clk) a;
                  endproperty

                  property p2;
                    @(posedge clk) cb_with_input.a;
                  endproperty

                  a1: assert property (p1);
                  a2: assert property (cb_with_input.p1);
                  a3: assert property (p2);
                  a4: assert property (cb_without_input.p1);
                endmodule"##,
            Ok((_, _))
        );
    }
}

#[test]
fn debug() {
    //nom_tracable::statistics(Span::new_extra("", SpanInfo::default()));
}
