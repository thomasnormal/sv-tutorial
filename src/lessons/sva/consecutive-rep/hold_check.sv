module hold_check(input logic clk, start, busy);

  property busy_hold_p;
    @(posedge clk)
      // TODO: after start pulses, busy must stay high for exactly 3 consecutive cycles
      ;
  endproperty

  busy_hold_a: assert property (busy_hold_p);

endmodule
