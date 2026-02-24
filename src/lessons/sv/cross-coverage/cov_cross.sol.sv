module cov_cross;
  bit clk = 0;
  bit [1:0] op;
  bit mode;
  always #5 clk = ~clk;

  covergroup cg_cross @(posedge clk);
    cp_op: coverpoint op {
      bins add = {2'd0};
      bins sub = {2'd1};
      bins mul = {2'd2};
      bins div = {2'd3};
    }

    cp_mode: coverpoint mode {
      bins user = {1'b0};
      bins kernel = {1'b1};
    }

    op_x_mode: cross cp_op, cp_mode;
  endgroup

  cg_cross cov = new;

  initial begin
    op = 0;
    mode = 0;
    repeat (8) begin
      @(posedge clk);
      op <= op + 1'b1;
      mode <= ~mode;
    end
    #1 $finish;
  end
endmodule
