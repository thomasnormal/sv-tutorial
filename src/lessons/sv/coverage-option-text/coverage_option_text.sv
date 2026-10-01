module tb;
  logic [1:0] value = 0;

  covergroup coverage_model;
    cp_value: coverpoint value {
      bins values[] = {[0:3]};
    }
  endgroup

  coverage_model coverage = new;

  initial begin
    if (coverage.option.comment == "") begin
      $display("FAIL: starter rejected the empty default comment");
      $finish;
    end

    coverage.option.comment = "runtime coverage comment";
    value = 2;
    coverage.sample();

    if (coverage.option.comment == "runtime coverage comment")
      $display("PASS: comment=%s", coverage.option.comment);
    else
      $display("FAIL: comment=%s", coverage.option.comment);
    $finish;
  end
endmodule
