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


def _running_in_pyodide():
    try:
        import js  # noqa: F401
        return True
    except Exception:
        return False


if __name__ == "__main__" and not _running_in_pyodide():
    import argparse
    from pathlib import Path
    from cocotb.runner import get_runner

    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser()
    parser.add_argument("-m", "--module", default=str(here / "adder.sv"))
    parser.add_argument("-t", "--toplevel", default="adder")
    parser.add_argument("--sim", default="icarus", choices=["icarus", "verilator"])
    args = parser.parse_args()

    runner = get_runner(args.sim)
    runner.build(
        verilog_sources=[args.module],
        toplevel=args.toplevel,
        build_dir=str(here / "sim_build"),
        always=True,
    )
    runner.test(
        toplevel=args.toplevel,
        test_module="test_adder",
        python_search=[str(here)],
    )
