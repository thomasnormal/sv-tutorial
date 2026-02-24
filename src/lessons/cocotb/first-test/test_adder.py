import cocotb
from cocotb.triggers import Timer


async def check(dut, a, b, expected):
    dut.A.value = a
    dut.B.value = b
    await Timer(2, units="ns")   # let combinational logic settle
    assert dut.X.value == expected, f"{a} + {b} = {dut.X.value} (expected {expected})"


@cocotb.test()
async def adder_test(dut):
    await check(dut,  0,  0,  0)
    await check(dut,  9,  6, 15)
    await check(dut, 15, 15, 30)
    await check(dut,  8,  9, 17)
