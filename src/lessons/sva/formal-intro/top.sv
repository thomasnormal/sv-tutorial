module top(
  input  logic clk, rst,
  output logic [3:0] cnt
);
  always_ff @(posedge clk)
    if (rst) cnt <= 4'b0;
    else     cnt <= cnt + 1;

  // TODO: assert that when rst fires, cnt is 0 on the next cycle
endmodule
