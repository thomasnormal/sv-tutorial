module fifo_checker #(parameter int DEPTH = 8) (
  input logic clk,
  input logic wr_en, rd_en,
  input logic full, empty,
  input logic [$clog2(DEPTH):0] count  // 0 to DEPTH
);
  always @(posedge clk) begin
    assert (!wr_en || !full)
      else $error("Write to full FIFO!");
    assert (!rd_en || !empty)
      else $error("Read from empty FIFO!");
    assert (!(wr_en && rd_en))
      else $error("Simultaneous read and write on 1-port FIFO!");
    assert (count <= DEPTH)
      else $error("FIFO count %0d exceeds DEPTH %0d!", count, DEPTH);
  end
endmodule
