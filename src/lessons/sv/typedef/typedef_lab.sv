package typedef_pkg;
  // The aliases are ready to use; the exercise is wiring them through the
  // module and its intermediate signals.
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

  // TODO: use the aliases for the intermediate values and connect the
  //       sum, result, selected lane, and lane_copy with continuous assigns.
endmodule
