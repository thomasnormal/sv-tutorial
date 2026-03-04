// A class bundles data and methods that operate on it.
// Unlike structs, classes are reference types: a variable holds a *handle*
// (pointer) to an object, not the object itself.

class mem_item;
  // TODO: declare four fields
  //   bit         we
  //   logic [3:0] addr
  //   logic [7:0] wdata
  //   logic [7:0] rdata

  // Constructor — called with 'new(we, addr, wdata)'
  function new(bit we, logic [3:0] addr, logic [7:0] wdata);
    // TODO: store each argument into the matching field using this.field = arg
    //       leave rdata at its default value (0)
  endfunction

  // Pretty-print for $display
  function string convert2string();
    // TODO: return a formatted string:
    //   if we: "WR[<addr>]=<wdata>"
    //   else:  "RD[<addr>]"
    // Hint: use $sformatf("WR[%0d]=%0h", addr, wdata)
  endfunction
endclass

module mem_item_tb;
  initial begin
    mem_item t1, t2;

    // Create the first object and verify convert2string
    t1 = new(1, 4'd5, 8'hA5);
    $display("t1: %s", t1.convert2string());

    // Assign handle — t2 and t1 point to the SAME object
    t2 = t1;
    t2.wdata = 8'hFF;
    assert (t1.wdata == 8'hFF) else $fatal(1, "FAIL: handle assignment should share the object");

    // Create a new independent object
    t2 = new(0, 4'd3, 8'h00);
    $display("t2: %s", t2.convert2string());
    assert (t1.wdata == 8'hFF) else $fatal(1, "FAIL: t1 should be unchanged after t2 = new(...)");

    $display("PASS");
  end
endmodule
