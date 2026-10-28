// Parameterized bit array: elaboration chooses one operation and replicates it.
module generate_lab #(
  parameter int WIDTH = 4,
  parameter bit USE_XOR = 1'b1
) (
  input  logic [WIDTH-1:0] a, b,
  output logic [WIDTH-1:0] y
);
  generate
    // TODO: add a generate-if with named xor and or branches.
    //       In each branch, use a generate-for to drive every y[i].
  endgenerate
endmodule
