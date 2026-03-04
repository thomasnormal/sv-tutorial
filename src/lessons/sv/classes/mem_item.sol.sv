class mem_item;
  bit         we;
  logic [3:0] addr;
  logic [7:0] wdata;
  logic [7:0] rdata;

  function new(bit we, logic [3:0] addr, logic [7:0] wdata);
    this.we    = we;
    this.addr  = addr;
    this.wdata = wdata;
    this.rdata = 8'h00;
  endfunction

  function string convert2string();
    if (we)
      return $sformatf("WR[%0d]=%0h", addr, wdata);
    else
      return $sformatf("RD[%0d]", addr);
  endfunction
endclass

module mem_item_tb;
  initial begin
    mem_item t1, t2;

    t1 = new(1, 4'd5, 8'hA5);
    $display("t1: %s", t1.convert2string());

    t2 = t1;
    t2.wdata = 8'hFF;
    assert (t1.wdata == 8'hFF) else $fatal(1, "FAIL: handle assignment should share the object");

    t2 = new(0, 4'd3, 8'h00);
    $display("t2: %s", t2.convert2string());
    assert (t1.wdata == 8'hFF) else $fatal(1, "FAIL: t1 should be unchanged after t2 = new(...)");

    $display("PASS");
  end
endmodule
