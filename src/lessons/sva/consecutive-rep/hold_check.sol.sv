module hold_check(input logic clk, start, busy);

  property busy_hold_p;
    @(posedge clk) start |=> busy[*3];
  endproperty

  busy_hold_a: assert property (busy_hold_p);

endmodule
