module adder (
  input  logic [3:0] A, B,
  output logic [4:0] X
);
  // Keep the simulator alive long enough for the cocotb VPI startup callback.
  initial #1;

  // TODO: compute X as the sum of A and B
endmodule
