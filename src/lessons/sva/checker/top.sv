// A checker is an encapsulated, reusable assertion block — write once, instantiate anywhere.
// (Using module here since the checker keyword is not yet lowered by the WASM tool;
//  semantics are identical for verification purposes.)

// Checker 1: req must be acknowledged within 1-3 cycles
module handshake_check(input logic clk, req, ack);
  property p_req_ack;
    @(posedge clk)
      // TODO 1: when req fires, ack must arrive within 1–3 cycles (use ##[m:n])
      ;
  endproperty
  req_ack_a: assert property (p_req_ack);
endmodule

// Checker 2: while valid is high, data must not change
module data_stable_check(input logic clk, valid, input logic [7:0] data);
  property p_data_stable;
    @(posedge clk)
      // TODO 2: while valid is high, data must remain stable on the next cycle
      //         hint: valid implies $stable(data) on the following cycle
      ;
  endproperty
  data_stable_a: assert property (p_data_stable);
endmodule

// Instantiate both checkers for two independent bus channels
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
