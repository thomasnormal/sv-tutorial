module pipeline_check(
  input logic        clk,
  input logic        valid_in,
  input logic [7:0]  in_data,
  input logic [7:0]  out_data
);

  property pipe_latency_p;
    int v;
    @(posedge clk)
      // TODO: capture in_data when valid_in fires, then check out_data equals it 3 cycles later
      ;
  endproperty

  pipe_latency_a: assert property (pipe_latency_p);

endmodule
