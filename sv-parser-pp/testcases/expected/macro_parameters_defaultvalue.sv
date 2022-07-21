`define connect(NAME, INDEX = 0) \
  assign NAME``_``INDEX``__x = NAME[INDEX].x; \
  assign NAME``_``INDEX``__y = NAME[INDEX].y;

module a ();

  assign a_0__x = a[0].x; 
  assign a_0__y = a[0].y; assign a_1__x = a[1].x; 
  assign a_1__y = a[1].y; endmodule
