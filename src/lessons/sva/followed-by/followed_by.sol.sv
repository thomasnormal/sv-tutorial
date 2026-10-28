module top(
  input logic clk,
  input logic burst_start,
  input logic burst_beat,
  input logic data_ok
);
  sequence burst_read;
    burst_start ##1 burst_beat ##1 burst_beat;
  endsequence

  property overlap_followed;
    @(posedge clk) burst_read #-# data_ok;
  endproperty

  property nonoverlap_followed;
    @(posedge clk) burst_read #=# data_ok;
  endproperty

  property ordinary_implication;
    @(posedge clk) burst_start |=> data_ok;
  endproperty

  overlap_followed_a:    assert property (overlap_followed);
  nonoverlap_followed_a:  assert property (nonoverlap_followed);
  ordinary_implication_a: assert property (ordinary_implication);
endmodule
