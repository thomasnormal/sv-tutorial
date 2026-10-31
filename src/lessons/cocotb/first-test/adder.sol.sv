module adder (
  input  logic [3:0] A, B,
  output logic [4:0] X
);
  // Keep the simulator alive long enough for the cocotb VPI startup callback.
  initial #1;

  always @(*) X = A + B;
endmodule
