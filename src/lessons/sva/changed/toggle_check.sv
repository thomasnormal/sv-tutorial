module toggle_check(input logic clk, update, input logic [7:0] data);

  property p_data_changes;
    @(posedge clk)
      // TODO: when update is high, data must change on the very next cycle
      ;
  endproperty

  data_changes_a: assert property (p_data_changes);

endmodule
