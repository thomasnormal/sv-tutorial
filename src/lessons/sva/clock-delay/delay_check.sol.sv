module delay_check(input logic clk, mem_req, mem_ack);

  sequence delayed_ack;
    mem_ack;
  endsequence

  property mem_latency_p;
    @(posedge clk) mem_req |-> ##[2:5] delayed_ack;
  endproperty

  mem_latency_a: assert property (mem_latency_p);

endmodule
