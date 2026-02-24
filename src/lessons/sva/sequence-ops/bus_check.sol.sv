module bus_check(input logic clk, valid, ready);

  property p_transfer;
    @(posedge clk) valid |-> (valid[*4]) intersect (ready[*4]);
  endproperty

  transfer_a: assert property (p_transfer);

endmodule
