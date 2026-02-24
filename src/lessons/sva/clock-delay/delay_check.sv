module delay_check(input logic clk, mem_req, mem_ack);

  property mem_latency_p;
    @(posedge clk)
      // TODO: mem_req |-> ##[2:5] mem_ack;
      ;
  endproperty

  mem_latency_a: assert property (mem_latency_p);

endmodule
