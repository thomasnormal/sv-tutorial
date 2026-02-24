module pipeline_check(
  input logic        clk,
  input logic        valid_in,
  input logic [7:0]  in_data,
  input logic [7:0]  out_data
);

  property pipe_latency_p;
    int v;
    @(posedge clk)
      (valid_in, v = in_data) |=> ##2 (out_data == v);
  endproperty

  pipe_latency_a: assert property (pipe_latency_p);

endmodule
