module reg_en (
  input  logic       clk,
  input  logic       rst,
  input  logic       en,
  input  logic [3:0] d,
  output logic [3:0] q
);
  always_ff @(posedge clk) begin
    if (rst)      q <= 4'd0;
    else if (en)  q <= d;
  end
endmodule
