`define A "aaa"
`define \B "bbb"
module M;
  initial begin
    $display("aaa");
    $display("aaa" );
    $display("bbb");
    $display("bbb" );
  end
endmodule
