module operator_lab (
  input  logic [3:0]        a, b,
  input  logic              choose_a,
  input  logic signed [3:0] signed_a, signed_b,
  output logic [3:0]        bitwise_and,
  output logic [3:0]        bitwise_or,
  output logic              any_set,
  output logic [3:0]        chosen,
  output logic [3:0]        wrapped_sum,
  output logic [4:0]        full_sum,
  output logic signed [3:0] signed_sum
);
  assign bitwise_and = a & b;
  assign bitwise_or  = a | b;
  assign any_set     = |a;
  assign chosen      = choose_a ? a : b;
  assign wrapped_sum = a + b;
  assign full_sum    = {1'b0, a} + {1'b0, b};
  assign signed_sum  = signed_a + signed_b;
endmodule
