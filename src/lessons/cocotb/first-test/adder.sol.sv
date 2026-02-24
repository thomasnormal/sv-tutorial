module adder (
  input  logic [3:0] A, B,
  output logic [4:0] X
);
  assign X = A + B;
endmodule
