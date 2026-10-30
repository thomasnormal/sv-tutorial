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
  // TODO: add continuous assignments for the bitwise, reduction, ternary,
  //       unsigned-sum, and signed-sum outputs described in the lesson.
endmodule
