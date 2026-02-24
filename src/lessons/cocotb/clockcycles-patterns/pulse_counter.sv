module pulse_counter (
  input  logic       clk,
  input  logic       rst,
  input  logic       pulse,
  output logic [3:0] count
);
  always_ff @(posedge clk) begin
    // TODO: clear on reset, otherwise increment when pulse is high.
  end
endmodule
