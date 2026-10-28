module counter_checker (
  input logic       clk,
  input logic       rst_n,
  input logic       en,
  input logic [7:0] count
);
  property count_step;
    @(posedge clk) disable iff (!rst_n)
      // TODO: when en is high, count increments on the following edge
      ;
  endproperty

  count_step_a: assert property (count_step);
endmodule

// Attach the checker without editing the counter's RTL source.
// TODO: bind counter to one counter_checker instance with named ports.
