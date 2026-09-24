// Dynamic arrays resize at runtime; queues grow and shrink automatically.
// Both are essential for testbench data structures.
//
// Dynamic array:  logic [3:0] name[];    // declare (empty — not yet allocated)
//                 name = new[n];         // allocate n elements inside initial
//
// Queue:          logic [3:0] name[$];   // unbounded, initially empty
//                 name.push_back(v);     // append to tail
//                 name.pop_front();      // remove and return head

module addr_buf_tb;

  // TODO 1: declare a dynamic array: logic [3:0] addrs[]
  //         (declaration goes here at module scope, before initial)

  logic [3:0] q[$];   // queue — already declared for you

  initial begin
    // TODO 2: allocate 8 elements in addrs using new[8]

    // Fill the dynamic array with addresses 0..7 (already done — shows the pattern)
    for (int i = 0; i < addrs.size(); i++)
      addrs[i] = 4'(i);

    $display("Array size: %0d  first=%0d  last=%0d",
             addrs.size(), addrs[0], addrs[addrs.size()-1]);

    // TODO 3: push the first four elements of addrs into q using push_back

    $display("Queue size after push: %0d", q.size());
    assert (q.size() == 4) else $fatal(1, "FAIL: expected 4 elements after push_back");

    // TODO 4: pop all elements from q using pop_front inside a while loop
    //         $display each value as "pop: <value>"
    //         A variable declared inside the loop needs 'automatic' for its
    //         initializer to run on every iteration:
    //           automatic logic [3:0] v = q.pop_front();

    assert (q.size() == 0) else $fatal(1, "FAIL: queue should be empty");
    $display("PASS");
  end
endmodule
