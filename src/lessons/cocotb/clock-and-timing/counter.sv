module counter (
  input  logic       clk, rst,
  output logic [3:0] count
);
  always_ff @(posedge clk) begin
    // TODO: reset count to 0 when rst is high, otherwise increment
  end
endmodule
