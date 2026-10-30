module monitor(input logic clk, req, gnt);

  // When req goes high, gnt must follow within 1–3 cycles.
  property req_then_gnt;
    @(posedge clk)
      req |-> ##[1:3] gnt;
  endproperty

  // TODO: Register a named checker for req_then_gnt outside procedural code.
  // Give it a searchable label and report which timing guarantee was missed
  // whenever a request is not followed by a grant in the allowed window.
  // TODO: Add a coverage action for the same property that prints PASS and
  // the current simulation time whenever an assertion attempt is observed.

endmodule
