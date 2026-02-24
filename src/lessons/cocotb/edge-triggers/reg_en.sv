module reg_en (
  input  logic       clk,
  input  logic       rst,
  input  logic       en,
  input  logic [3:0] d,
  output logic [3:0] q
);
  always_ff @(posedge clk) begin
    // TODO: clear q on reset, otherwise load d when en is high.
  end
endmodule
