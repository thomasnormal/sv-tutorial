module hold_check(input logic clk, start, busy);

  sequence busy_run;
    busy[*3];
  endsequence

  property busy_hold_p;
    @(posedge clk) start |=> busy_run;
  endproperty

  busy_hold_a: assert property (busy_hold_p);

endmodule
