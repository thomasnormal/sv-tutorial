module counter (
  input  logic       clk,
  input  logic       rst_n,
  input  logic       en,
  output logic [7:0] count
);
  // This is the Part 1 counter interface reused by the bound checker.
  always_ff @(posedge clk) begin
    if (!rst_n)  count <= 8'd0;
    else if (en) count <= count + 8'd1;
  end
endmodule
