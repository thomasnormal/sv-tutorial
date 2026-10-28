module abort_check(input logic clk, start, ack, err);

  sequence ack_window;
    // TODO: match an acknowledgement within four cycles
    1'b0;
  endsequence

  // Spec: after start, ack must arrive within 4 cycles.
  // If err fires mid-transfer, fail immediately.
  property p_burst_ok;
    @(posedge clk)
      // TODO: if err fires while ack_window is active, reject the property
      start |=> reject_on(err) ack_window;
  endproperty

  // TODO: assert p_burst_ok on every clock edge.

endmodule
