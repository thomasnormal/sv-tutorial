interface mem_if (input logic clk);
  logic        we;
  logic [3:0]  addr;
  logic [7:0]  wdata;
  logic [7:0]  rdata;

  function string sprint();
    string summary;
    summary = $sformatf(
      "we=%0b addr=%0h wdata=%0h rdata=%0h",
      we, addr, wdata, rdata);
    return summary;
  endfunction
endinterface
