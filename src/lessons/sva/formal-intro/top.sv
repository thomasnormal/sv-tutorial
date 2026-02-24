module top(
  input  logic clk, rst,
  output logic [3:0] cnt
);
  always_ff @(posedge clk)
    if (rst) cnt <= 4'b0;
    else     cnt <= cnt + 1;

  // TODO: rst_clears: assert property (
  //   @(posedge clk) rst |=> (cnt == 0));
endmodule
