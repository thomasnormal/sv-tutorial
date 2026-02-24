module adder (
  input  logic [7:0] a, b,
  output logic [7:0] sum,
  output logic       carry
);
  assign {carry, sum} = a + b;
endmodule
