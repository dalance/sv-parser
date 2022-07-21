/* IEEE1800-2017 Clause 22.5.1 page 677
* NOTE: Illegal cases are not included in this testcase.
*/

`define D(x,y) initial $display("start", x , y, "end");

module m;
initial begin
  $display("start", "msg1" , "msg2", "end");
  $display("start", " msg1" , , "end");
  $display("start",  , "msg2 ", "end");
  $display("start",  , , "end");
  $display("start",  , , "end");
end
endmodule
