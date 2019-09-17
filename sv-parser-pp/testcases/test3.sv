`define connect(NAME, INDEX = 0) \
  assign NAME``_``INDEX``__x = NAME[INDEX].x; \
  assign NAME``_``INDEX``__y = NAME[INDEX].y;

module a ();

  `connect(a);
  `connect(a, 1);

endmodule
