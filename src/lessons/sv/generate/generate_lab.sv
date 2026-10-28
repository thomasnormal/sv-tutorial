// Parameterized bit array: elaboration chooses one operation and replicates it.
module generate_lab #(
  parameter int WIDTH = 4,
  parameter bit USE_XOR = 1'b1
) (
  input  logic [WIDTH-1:0] a, b,
  output logic [WIDTH-1:0] y
);
  generate
    // The parameter chooses the operation; your task is to replicate each
    // one-bit lane across the vector in both branches.
    if (USE_XOR) begin : gen_xor
      // TODO: add a named generate-for from 0 through WIDTH-1 and assign
      //       each y[i] to the XOR of a[i] and b[i].
    end else begin : gen_or
      // TODO: add the matching generate-for and assign each y[i] to the OR
      //       of a[i] and b[i].
    end
  endgenerate
endmodule
