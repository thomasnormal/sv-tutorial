module monitor(input logic clk, req, gnt);

  // When req goes high, gnt must follow within 1–3 cycles.
  property req_then_gnt;
    @(posedge clk)
      req |-> ##[1:3] gnt;
  endproperty

  // TODO: assert property (req_then_gnt) — print an error when gnt is late
  // TODO: cover property (req_then_gnt) — count how many times the property fired

endmodule
