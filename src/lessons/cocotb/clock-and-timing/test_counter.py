import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles


@cocotb.test()
async def counter_test(dut):
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())   # run clock in background

    # Reset
    dut.rst.value = 1
    await RisingEdge(dut.clk)         # @(posedge clk)
    dut.rst.value = 0

    # Count 5 cycles
    await ClockCycles(dut.clk, 5)     # repeat(5) @(posedge clk)
    assert dut.count.value == 5, f"Expected 5, got {dut.count.value}"

    # Reset mid-run
    dut.rst.value = 1
    await RisingEdge(dut.clk)
    dut.rst.value = 0
    assert dut.count.value == 0, f"Expected 0 after reset, got {dut.count.value}"
