/* IEEE1800-2017 Clause 22.5.1 page 678
* NOTE: Illegal cases are not included in this testcase.
* NOTE: Use of EMPTY is suggested on page 679
*/

`define MACRO1(a=5,b="B",c) $display(a,,b,,c);
`define MACRO2(a=5, b, c="C") $display(a,,b,,c);
`define MACRO3(a=5, b=0, c="C") $display(a,,b,,c);

`define EMPTY

module m;
initial begin
  `MACRO1 ( , 2, 3 )
  `MACRO1 ( 1 , , 3 )
  `MACRO1 ( , 2, )
  `MACRO2 (1, , 3)
  `MACRO2 (, 2, )
  `MACRO2 (, 2)
  `MACRO3 ( 1 )
  `MACRO3 ( )

  `MACRO3 (`EMPTY,`EMPTY,`EMPTY)
end
endmodule
