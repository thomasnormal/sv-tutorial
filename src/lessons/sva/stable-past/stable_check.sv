module stable_check(
  input logic clk,
  input logic valid, ready,
  input logic [7:0] data
);
  property data_stable_p;
    @(posedge clk)
      // TODO: while valid is high and ready is low, data must not change on the next cycle
      ;
  endproperty

  data_stable_a: assert property (data_stable_p);

endmodule
