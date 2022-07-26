// Based on last example of IEEE1800-2017 Clause 22.5.1, page 680.
`define APPEND_SVH(path) `"path.svh`"
module and_op (a, b, c);
output a;
input b, c;

and a1 (a,b,c);

endmodule
