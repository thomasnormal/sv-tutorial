module arrays_lab (
  input  logic [7:0] packed_in,
  input  logic [7:0] byte0, byte1,
  output logic [7:0] packed_value,
  output logic [7:0] unpacked_total,
  output logic [1:0] packed_lanes,
  output logic [1:0] unpacked_length
);
  // These declarations show the two shapes; the exercise connects them.
  logic [1:0][3:0] packed_grid;
  logic [7:0]       byte_mem [0:1];

  // TODO: assign packed_in into packed_grid, byte0/byte1 into byte_mem,
  //       then expose the packed value, unpacked sum, and both $size results.
endmodule
