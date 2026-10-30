module let_check(
  input logic clk,
  input logic valid,
  input logic ready,
  input logic [7:0] data
);
  // TODO: define a parameterised let expression for a held data bus.
  //       Use it in the property below instead of repeating the expression.

  property data_stable_p;
    @(posedge clk)
      // TODO: while valid is high and ready is low, data stays stable
      ;
  endproperty

  data_stable_a: assert property (data_stable_p);
endmodule
