module toggle_check(input logic clk, update, input logic [7:0] data);

  property p_data_changes;
    @(posedge clk)
      // TODO: update |=> $changed(data);
      ;
  endproperty

  data_changes_a: assert property (p_data_changes);

endmodule
