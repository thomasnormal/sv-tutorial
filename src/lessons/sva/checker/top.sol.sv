module handshake_check(input logic clk, req, ack);
  property p_req_ack;
    @(posedge clk) req |=> ##[1:3] ack;
  endproperty
  req_ack_a: assert property (p_req_ack);
endmodule

module data_stable_check(input logic clk, valid, input logic [7:0] data);
  property p_data_stable;
    @(posedge clk) valid |-> $stable(data);
  endproperty
  data_stable_a: assert property (p_data_stable);
endmodule

module top(
  input logic       clk,
  input logic       req1, ack1,
  input logic       req2, ack2,
  input logic       valid1, valid2,
  input logic [7:0] data1, data2
);

  handshake_check  c1(.clk, .req(req1), .ack(ack1));
  handshake_check  c2(.clk, .req(req2), .ack(ack2));

  data_stable_check s1(.clk, .valid(valid1), .data(data1));
  data_stable_check s2(.clk, .valid(valid2), .data(data2));

endmodule
