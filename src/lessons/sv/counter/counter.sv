module counter (
  input  logic       clk, rst_n, en,
  output logic [7:0] count
);
  always_ff @(posedge clk) begin
    // TODO: synchronous reset, then increment when en
  end
endmodule
