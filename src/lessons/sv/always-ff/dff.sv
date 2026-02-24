module dff (
  input  logic clk, rst_n, d,
  output logic q
);
  always_ff @(posedge clk) begin
    // TODO: if (!rst_n) q <= 0; else q <= d;
  end
endmodule
