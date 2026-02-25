package mem_pkg;
  typedef struct packed {
    logic        we;    // write-enable: 1 = write, 0 = read
    logic [3:0]  addr;  // address: which of the 16 memory locations to access
    logic [7:0]  wdata; // write data: value to store when we = 1
  } mem_cmd_t;
endpackage
