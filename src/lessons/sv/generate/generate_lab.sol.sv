// Parameterized bit array: elaboration chooses one operation and replicates it.
module generate_lab #(
  parameter int WIDTH = 4,
  parameter bit USE_XOR = 1'b1
) (
  input  logic [WIDTH-1:0] a, b,
  output logic [WIDTH-1:0] y
);
  generate
    if (USE_XOR) begin : gen_xor
      for (genvar i = 0; i < WIDTH; i++) begin : gen_xor_bit
        assign y[i] = a[i] ^ b[i];
      end
    end else begin : gen_or
      for (genvar i = 0; i < WIDTH; i++) begin : gen_or_bit
        assign y[i] = a[i] | b[i];
      end
    end
  endgenerate
endmodule
