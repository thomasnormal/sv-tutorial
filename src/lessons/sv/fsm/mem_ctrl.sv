typedef enum logic [1:0] { IDLE, READING, WRITING } ctrl_state_t;

module mem_ctrl (
  input  logic clk,         // clock: state updates on the rising edge
  input  logic rst_n,       // active-low reset: holds state = IDLE while low
  input  logic cmd_valid,   // request present on bus
  input  logic cmd_we,      // 1 = write, 0 = read
  output logic sram_we,     // write-enable to SRAM
  output logic ready        // controller ready for next command
);
  ctrl_state_t state, next;

  // ── State register ──────────────────────────────────────────────────────────
  always_ff @(posedge clk)
    if (!rst_n) state <= IDLE;
    else        state <= next;

  // ── Next-state and output logic ─────────────────────────────────────────────
  always_comb begin
    next    = state;
    sram_we = 1'b0;
    ready   = 1'b0;
    case (state)
      IDLE: begin
        ready = 1'b1;
        // TODO: transition to WRITING or READING based on cmd_valid and cmd_we
      end
      READING: begin
        // TODO: set sram_we and next state
      end
      WRITING: begin
        // TODO: set sram_we and next state
      end
      default: next = IDLE;
    endcase
  end
endmodule
