module top(
  input logic clk,
  input logic burst_start,
  input logic burst_beat,
  input logic data_ok
);
  sequence burst_read;
    // TODO: describe a start followed by two beat cycles
  endsequence

  property overlap_followed;
    @(posedge clk)
      // TODO: require data_ok when burst_read ends (overlapped)
      ;
  endproperty

  property nonoverlap_followed;
    @(posedge clk)
      // TODO: require data_ok one cycle after burst_read ends (non-overlapped)
      ;
  endproperty

  property ordinary_implication;
    @(posedge clk)
      // TODO: express the same trigger with |=> for comparison
      ;
  endproperty

  overlap_followed_a:    assert property (overlap_followed);
  nonoverlap_followed_a:  assert property (nonoverlap_followed);
  ordinary_implication_a: assert property (ordinary_implication);
endmodule
