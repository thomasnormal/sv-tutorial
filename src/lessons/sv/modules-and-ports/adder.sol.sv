module adder(
  input  logic [7:0] a,
  input  logic [7:0] b,
  output logic [7:0] sum
);
  assign sum = a + b;
endmodule
