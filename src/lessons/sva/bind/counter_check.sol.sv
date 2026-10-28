module counter_checker (
  input logic       clk,
  input logic       rst_n,
  input logic       en,
  input logic [7:0] count
);
  property count_step;
    @(posedge clk) disable iff (!rst_n)
      en |=> count == $past(count) + 8'd1;
  endproperty

  count_step_a: assert property (count_step);
endmodule

bind counter counter_checker count_check_i (
  .clk   (clk),
  .rst_n (rst_n),
  .en    (en),
  .count (count)
);
