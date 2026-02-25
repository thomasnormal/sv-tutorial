typedef enum logic [1:0] { IDLE, CMD, READ, WRITE } ctrl_state_t;

module ctrl_display (
  input  ctrl_state_t state,
  output logic        reading,
  output logic        writing
);
  always_comb begin
    reading = 1'b0;
    writing = 1'b0;
    case (state)
      READ:  reading = 1'b1;
      WRITE: writing = 1'b1;
      default: ;
    endcase
  end
endmodule
