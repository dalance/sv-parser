module A;
`ifdef OPT_1
  //wire a = 1'b1;
`else
  wire a = 1'b0;
`endif
`ifdef DEBUG
  `ifdef OPT_2
  //wire b = 1'b1;
  `else
  wire b = 1'b0;
  `endif
`endif
endmodule
