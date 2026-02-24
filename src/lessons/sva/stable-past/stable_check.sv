module stable_check(
  input logic clk,
  input logic valid, ready,
  input logic [7:0] data
);
  property data_stable_p;
    @(posedge clk)
      // TODO: (valid && !ready) |=> $stable(data);
      ;
  endproperty

  data_stable_a: assert property (data_stable_p);

endmodule
