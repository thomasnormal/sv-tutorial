module counter (
  input  logic       clk, rst_n, en,
  output logic [7:0] count
);
  always_ff @(posedge clk) begin
    if (!rst_n)  count <= 8'd0;
    else if (en) count <= count + 8'd1;
  end
endmodule
