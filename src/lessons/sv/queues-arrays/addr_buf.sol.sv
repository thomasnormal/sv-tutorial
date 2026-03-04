module addr_buf_tb;

  logic [3:0] addrs[];
  logic [3:0] q[$];

  initial begin
    addrs = new[8];

    for (int i = 0; i < addrs.size(); i++)
      addrs[i] = logic'(i);

    $display("Array size: %0d  first=%0d  last=%0d",
             addrs.size(), addrs[0], addrs[addrs.size()-1]);

    for (int i = 0; i < 4; i++)
      q.push_back(addrs[i]);

    $display("Queue size after push: %0d", q.size());

    while (q.size() > 0) begin
      logic [3:0] v = q.pop_front();
      $display("pop: %0d", v);
    end

    assert (q.size() == 0) else $fatal(1, "FAIL: queue should be empty");
    $display("PASS");
  end
endmodule
