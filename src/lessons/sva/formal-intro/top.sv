module top(
  input  logic clk, rst,
  output logic [3:0] cnt
);
  always_ff @(posedge clk)
    if (rst) cnt <= 4'b0;
    else     cnt <= cnt + 1;

  property reset_clears;
    @(posedge clk)
      // TODO: when rst fires, cnt must be 0 on the next cycle
      ;
  endproperty

  reset_clears_a: assert property (reset_clears);
endmodule
