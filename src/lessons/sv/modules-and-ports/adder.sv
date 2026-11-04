module adder(
  // TODO: declare a as an 8-bit logic input
  input a,
  // TODO: declare b as an 8-bit logic input
  input b,
  // TODO: declare sum as an 8-bit logic output
  output sum
);
  // The arithmetic is supplied so this exercise stays focused on the port interface.
  assign sum = a + b;
endmodule
