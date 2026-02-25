module delay_check(input logic clk, mem_req, mem_ack);

  property mem_latency_p;
    @(posedge clk)
      // TODO: when mem_req fires, mem_ack must arrive within 2–5 clock cycles
      ;
  endproperty

  mem_latency_a: assert property (mem_latency_p);

endmodule
