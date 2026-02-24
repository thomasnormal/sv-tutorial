import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, RisingEdge


@cocotb.test()
async def pulse_counter_test(dut):
    cocotb.start_soon(Clock(dut.clk, 10, units="ns").start(start_high=False))

    dut.rst.value = 1
    dut.pulse.value = 0
    await ClockCycles(dut.clk, 1)
    assert dut.count.value == 0, f"Expected 0 after reset, got {dut.count.value}"

    dut.rst.value = 0
    pattern = [1, 0, 1, 1, 0, 0, 1, 1]
    expected = 0

    for i, p in enumerate(pattern):
        dut.pulse.value = p
        await RisingEdge(dut.clk)
        if p:
            expected = (expected + 1) & 0xF
        assert dut.count.value == expected, (
            f"cycle {i}: expected count={expected}, got {dut.count.value}"
        )

    dut.rst.value = 1
    await ClockCycles(dut.clk, 1)
    assert dut.count.value == 0, f"Expected 0 after second reset, got {dut.count.value}"
