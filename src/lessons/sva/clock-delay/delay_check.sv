module delay_check(input logic clk, mem_req, mem_ack);

  sequence delayed_ack;
    // TODO: match one sampled acknowledgement
    1'b0;
  endsequence

  property mem_latency_p;
    @(posedge clk)
      // TODO: when mem_req fires, delayed_ack must arrive within 2–5 cycles
      mem_req |-> ##[2:5] delayed_ack;
  endproperty

  // TODO: assert mem_latency_p on every clock edge.

endmodule
