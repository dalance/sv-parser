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
        //test!(
        //    many1(module_item),
        //    r##"Packet p; // declare a variable of class Packet
        //        p = new;  // initialize variable to a new allocated object
        //                  // of the class Packet"##,
        //    Ok((_, _))
        //);
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
        //test!(
        //    many1(module_item),
        //    r##"GetImp#(int) get_ref;
        //        Fifo#(int) fifo_obj = new;
        //        PutImp#(int) put_ref = fifo_obj;
        //        $cast(get_ref, put_ref);"##,
        //    Ok((_, _))
        //);
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
}

#[test]
fn debug() {}
