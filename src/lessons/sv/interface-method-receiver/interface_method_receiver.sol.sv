interface probe_if (input logic clk);
  string instance_path = $sformatf("%m");
  int answer = 0;

  function automatic string getPath();
    return instance_path;
  endfunction

  function automatic int getAnswer();
    return answer;
  endfunction
endinterface

class holder;
  virtual probe_if vif;
  string plain_path;
  string cast_path;
  string parenthesized_path;
  int cast_answer;
  int parenthesized_answer;

  function void report();
    plain_path = vif.getPath();
    cast_path = string'(vif.getPath());
    parenthesized_path = (vif.getPath());
    cast_answer = int'(vif.getAnswer());
    parenthesized_answer = (vif.getAnswer());
  endfunction
endclass

module tb;
  logic clk = 0;
  probe_if u_a(clk);
  probe_if u_b(clk);

  initial begin
    holder h;
    string expected_path;
    h = new;
    u_a.answer = 1;
    u_b.answer = 2;
    h.vif = u_b;
    h.report();
    expected_path = u_b.getPath();

    if (h.plain_path != expected_path ||
        h.cast_path != expected_path ||
        h.parenthesized_path != expected_path ||
        h.cast_answer != 2 || h.parenthesized_answer != 2) begin
      $display("FAIL: path=%s cast=%s paren=%s answers=%0d/%0d",
               h.plain_path, h.cast_path, h.parenthesized_path,
               h.cast_answer, h.parenthesized_answer);
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
