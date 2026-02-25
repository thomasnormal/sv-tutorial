module vacuous_demo (
  input logic clk, rst_n,
  input logic req, gnt
);
  // This property checks: whenever req rises, gnt follows within 2 clocks.
  // But if req NEVER rises in simulation, the assert still passes — vacuously.
  property req_gnt;
    @(posedge clk) disable iff (!rst_n)
      $rose(req) |-> ##[1:2] gnt;
  endproperty

  // TODO: add an assert property and a cover property for req_gnt

endmodule
