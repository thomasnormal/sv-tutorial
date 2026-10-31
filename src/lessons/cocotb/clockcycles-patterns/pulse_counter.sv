module pulse_counter (
  input  logic       clk,
  input  logic       rst,
  input  logic       pulse,
  output logic [3:0] count
);
  // Keep the simulator alive long enough for the cocotb VPI startup callback.
  initial #1;

  always_ff @(posedge clk) begin
    // TODO: clear on reset, otherwise increment when pulse is high.
  end
endmodule
