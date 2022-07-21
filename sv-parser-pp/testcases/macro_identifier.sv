`define A "aaa"
`define \B "bbb"
module M;
  initial begin
    $display(`A);
    $display(`\A );
    $display(`B);
    $display(`\B );
  end
endmodule
