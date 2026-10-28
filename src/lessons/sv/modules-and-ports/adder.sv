module adder(
  // TODO: make a an 8-bit logic input
  input a,
  // TODO: make b an 8-bit logic input
  input b,
  // TODO: make sum an 8-bit logic output
  output sum
);
  // The arithmetic is supplied so this exercise stays focused on the port interface.
  assign sum = a + b;
endmodule
