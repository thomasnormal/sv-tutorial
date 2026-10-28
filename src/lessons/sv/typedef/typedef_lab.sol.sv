package typedef_pkg;
  typedef logic [7:0] data_t;
  typedef logic [1:0] lane_t;
endpackage

import typedef_pkg::*;

module typedef_lab (
  input  data_t  left, right,
  input  lane_t  lane,
  output data_t  result,
  output logic [1:0] lane_copy
);
  data_t sum;
  lane_t selected_lane;

  assign sum           = left + right;
  assign selected_lane = lane;
  assign result        = sum ^ {6'b0, selected_lane};
  assign lane_copy     = selected_lane;
endmodule
