module dff (
  input  logic clk, rst_n, d,
  output logic q
);
  always_ff @(posedge clk) begin
    if (!rst_n) q <= 1'b0;
    else        q <= d;
  end
endmodule
