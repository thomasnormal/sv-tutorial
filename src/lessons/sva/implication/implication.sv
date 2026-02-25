module implication(input logic clk, req, ack);

  // Overlapping: ack must be high THE SAME cycle req is high
  property p_ol;
    // TODO: use |-> to check req and ack in the same cycle
  endproperty

  // Non-overlapping: ack must be high the NEXT cycle after req
  property p_nol;
    // TODO: use |=> to check ack arrives one cycle after req
  endproperty

  a_ol:  assert property (p_ol);
  a_nol: assert property (p_nol);

endmodule
