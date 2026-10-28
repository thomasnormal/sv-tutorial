module top(
  input  logic clk, rst,
  output logic [3:0] cnt
);
  always_ff @(posedge clk)
    if (rst) cnt <= 4'b0;
    else     cnt <= cnt + 1;

  // Reuse the one-cycle pattern from the implication lesson.
  sequence reset_event;
    // TODO: replace the placeholder with a sampled reset event
    1'b0;
  endsequence

  property reset_clears;
    @(posedge clk)
      // TODO: when reset_event fires, cnt must be 0 on the next cycle
      1'b0;
  endproperty

  // TODO: assert reset_clears on every clock edge.
endmodule
