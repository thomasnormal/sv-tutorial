module adder(
  input  [3:0] a,
  input  [3:0] b,
  output [4:0] sum
);
  assign sum = a + b;
endmodule

module top;
  reg  [3:0] a, b;
  wire [4:0] sum;

  // TODO: instantiate the adder module as 'dut'

  initial begin
    // TODO: test a=3, b=5, check sum==8
    // TODO: test a=15, b=1, check sum==16
    // TODO: print "ALL TESTS PASSED" and call $finish
  end
endmodule
