typedef enum logic { IDLE, BUSY } ctrl_state_t;

module mealy_ctrl (
  input  logic clk,
  input  logic rst_n,
  input  logic req,
  input  logic ack,
  output logic grant,
  output logic done,
  output logic busy
);
  ctrl_state_t state;

  // The state register is the only procedural block in this compact style.
  // TODO: reset to IDLE, then move to BUSY for a request and back on ack.
  //       Drive grant/done/busy from the current state and inputs.
endmodule
