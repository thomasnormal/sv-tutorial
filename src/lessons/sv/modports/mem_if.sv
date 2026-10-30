interface mem_if (input logic clk);
  logic        we;
  logic [3:0]  addr;
  logic [7:0]  wdata;
  logic [7:0]  rdata;

  function string sprint();
    return $sformatf("we=%0b addr=%0h wdata=%0h rdata=%0h",
                     we, addr, wdata, rdata);
  endfunction

  modport initiator (
    // TODO: list the command signals this side drives.
    // TODO: list the clock and read-data signals this side reads.
  );
  modport target (
    // TODO: list the command and clock signals this side reads.
    // TODO: list the read-data signal this side drives.
  );
endinterface
