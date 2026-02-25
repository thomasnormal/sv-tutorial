module abort_check(input logic clk, start, ack, err);

  // Spec: after start, ack must arrive within 4 cycles.
  // If err fires mid-transfer, fail immediately.
  property p_burst_ok;
    @(posedge clk)
      // TODO: after start, ack must arrive within 4 cycles; if err fires mid-burst, fail immediately
      ;
  endproperty

  burst_ok_a: assert property (p_burst_ok);

endmodule
