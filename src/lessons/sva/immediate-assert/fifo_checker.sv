module fifo_checker #(parameter int DEPTH = 8) (
  input logic clk,
  input logic wr_en, rd_en,
  input logic full, empty,
  input logic [$clog2(DEPTH):0] count  // 0 to DEPTH
);
  always @(posedge clk) begin
    // TODO 1: assert we never write when the FIFO is full
    //         hint: wr_en && full is illegal

    // TODO 2: assert we never read when the FIFO is empty
    //         hint: rd_en && empty is illegal

    // TODO 3: assert that read and write don't happen simultaneously
    //         (this is a 1-port FIFO — only one operation per cycle)

    // TODO 4: assert that count never exceeds DEPTH
  end
endmodule
