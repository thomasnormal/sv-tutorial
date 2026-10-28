module top(
  input  logic clk, rst,
  output logic [3:0] cnt
);
  always_ff @(posedge clk)
    if (rst) cnt <= 4'b0;
    else     cnt <= cnt + 1;

  sequence reset_event;
    rst;
  endsequence

  property reset_clears;
    @(posedge clk) reset_event |=> (cnt == 0);
  endproperty

  reset_clears_a: assert property (reset_clears);
endmodule
