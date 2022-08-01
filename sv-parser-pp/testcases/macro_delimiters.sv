// Multi-line macro defined with 2 trailing spaces before initial continuation.
// First line has no trailing space, second has trailing space, third is end.
// Macro contains 2-space indent, so indented usage gets extra.
// Delimiters (``) used before and after arguments.
`define connect(NAME, INDEX = 0)  \
  assign NAME``_``INDEX``__x = NAME[INDEX].x;\
  assign NAME``_``INDEX``__y = NAME[INDEX].y; \
  assign NAME``_``INDEX``__z = NAME[INDEX].z;

module M ();
  `connect(a)
  `connect(a, 1)
endmodule
