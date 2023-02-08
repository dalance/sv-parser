/* IEEE1800-2017 Clause 22.5.1 top of page 678
*/
`define MACRO1(a=5,b="B",c) $display(a,,b,,c);
`MACRO1(1) // Macro called without required argument `c`.

