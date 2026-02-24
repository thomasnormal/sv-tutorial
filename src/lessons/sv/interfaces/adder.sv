module adder (adder_if.slave bus);
  assign {bus.carry, bus.sum} = bus.a + bus.b;
endmodule
