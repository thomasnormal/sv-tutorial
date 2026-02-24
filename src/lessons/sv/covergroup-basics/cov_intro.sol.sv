module cov_intro;
  bit clk = 0;
  bit [1:0] opcode;
  always #5 clk = ~clk;

  covergroup cg_opcode @(posedge clk);
    coverpoint opcode;
  endgroup

  cg_opcode cov = new;

  initial begin
    opcode = 0;
    repeat (6) begin
      @(posedge clk);
      opcode <= opcode + 1'b1;
    end
    #1 $finish;
  end
endmodule
