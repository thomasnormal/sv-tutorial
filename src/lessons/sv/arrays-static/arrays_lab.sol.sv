module arrays_lab (
  input  logic [7:0] packed_in,
  input  logic [7:0] byte0, byte1,
  output logic [7:0] packed_value,
  output logic [7:0] unpacked_total,
  output logic [1:0] packed_lanes,
  output logic [1:0] unpacked_length
);
  logic [1:0][3:0] packed_grid;
  logic [7:0]       byte_mem [0:1];

  assign packed_grid   = packed_in;
  assign byte_mem[0]   = byte0;
  assign byte_mem[1]   = byte1;
  assign packed_value  = packed_grid;
  assign unpacked_total = byte_mem[0] + byte_mem[1];
  assign packed_lanes  = $size(packed_grid);
  assign unpacked_length = $size(byte_mem);
endmodule
