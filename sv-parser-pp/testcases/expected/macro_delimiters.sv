// Multi-line macro defined with 2 trailing spaces before initial continuation.
// First line has no trailing space, second has trailing space, third is end.
// Macro contains 2-space indent, so indented usage gets extra.
// Delimiters (``) used before and after arguments.
`define connect(NAME, INDEX = 0)  \
  assign NAME``_``INDEX``__x = NAME[INDEX].x;\
  assign NAME``_``INDEX``__y = NAME[INDEX].y; \
  assign NAME``_``INDEX``__z = NAME[INDEX].z;

module M ();
    assign a_0__x = a[0].x;
  assign a_0__y = a[0].y; 
  assign a_0__z = a[0].z;
    assign a_1__x = a[1].x;
  assign a_1__y = a[1].y; 
  assign a_1__z = a[1].z;
endmodule
