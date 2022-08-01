`define PATH included.svh
`define QUOTE(path) `"path`"
module and_op (a, b, c);
`include `QUOTE(`PATH)
endmodule
