module let_check(
  input logic clk,
  input logic valid,
  input logic ready,
  input logic [7:0] data
);
  let hold_bus(value, active, accepted) =
    !(active && !accepted) || $stable(value);

  property data_stable_p;
    @(posedge clk) hold_bus(data, valid, ready);
  endproperty

  data_stable_a: assert property (data_stable_p);
endmodule
