typedef enum logic [1:0] { IDLE, READING, WRITING } ctrl_state_t;

module mem_ctrl (
  input  logic clk,        // clock: state updates on the rising edge
  input  logic rst_n,      // active-low reset: holds state = IDLE while low
  input  logic cmd_valid,  // request present on bus
  input  logic cmd_we,     // 1 = write, 0 = read
  output logic sram_we,    // write-enable to SRAM
  output logic ready       // controller ready for next command
);
  ctrl_state_t state, next;

  always_ff @(posedge clk)
    if (!rst_n) state <= IDLE;
    else        state <= next;

  always_comb begin
    next    = state;
    sram_we = 1'b0;
    ready   = 1'b0;
    case (state)
      IDLE: begin
        ready = 1'b1;
        if (cmd_valid && cmd_we)  next = WRITING;
        if (cmd_valid && !cmd_we) next = READING;
      end
      READING: begin
        sram_we = 1'b0;
        next    = IDLE;
      end
      WRITING: begin
        sram_we = 1'b1;
        next    = IDLE;
      end
      default: next = IDLE;
    endcase
  end
endmodule
