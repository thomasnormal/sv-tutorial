module hold_check(input logic clk, start, busy);

  sequence busy_run;
    // TODO: match three consecutive busy samples
    1'b0;
  endsequence

  property busy_hold_p;
    @(posedge clk)
      // TODO: after start pulses, busy_run must follow
      start |=> busy_run;
  endproperty

  // TODO: assert busy_hold_p on every clock edge.

endmodule
