// Bundle all SRAM signals into one reusable port.
interface mem_if (input logic clk);
  logic        we;
  logic [3:0]  addr;
  logic [7:0]  wdata;
  logic [7:0]  rdata;

  function string sprint();
    string summary;
    // TODO: use $sformatf to capture all four live bus fields in summary.
    // TODO: return the formatted summary to the caller.
  endfunction
endinterface
