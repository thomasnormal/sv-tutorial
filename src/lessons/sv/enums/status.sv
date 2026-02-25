// Controller states for our SRAM memory controller
// TODO: define ctrl_state_t as a typedef enum with IDLE, CMD, READ, WRITE

module ctrl_display (
  input  logic [1:0] state,  // TODO: change type to ctrl_state_t
  output logic       reading,
  output logic       writing
);
  always_comb begin
    reading = 1'b0;
    writing = 1'b0;
    case (state)
      // TODO: add branches that set reading=1 or writing=1 using enum names
      default: ;
    endcase
  end
endmodule
