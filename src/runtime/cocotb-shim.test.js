import { execFileSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';

const SHIM = readFileSync(new URL('./cocotb-shim.py', import.meta.url), 'utf8');

function hasPython() {
  try {
    execFileSync('python3', ['--version'], { stdio: 'ignore' });
    return true;
  } catch {
    return false;
  }
}

// Runs a lesson-style cocotb test against the shim, with a stub `js` module
// that fires every registered trigger immediately and records its spec.
const HARNESS = String.raw`
import asyncio, json, sys, types
registered, logs = [], []
js = types.ModuleType('js')
js._cocotb_register_trigger = lambda s: registered.append(json.loads(s))
js._cocotb_get_signal = lambda name: 0
js._cocotb_set_signal = lambda name, val: None
js._cocotb_log = logs.append
js._cocotb_tests_done = lambda ok: None
sys.modules['js'] = js
cocotb = types.ModuleType('cocotb')
sys.modules['cocotb'] = cocotb
exec(sys.stdin.read(), cocotb.__dict__)

from cocotb.clock import Clock
from cocotb.triggers import ReadOnly, Timer

@cocotb.test()
async def test_lesson_api(dut):
    Clock(dut.clk, 10, unit="ns")
    await Timer(3, unit="ns")
    await Timer(2, units="ns")
    await ReadOnly()

async def main():
    task = asyncio.ensure_future(cocotb._run_all())
    while not task.done():
        await asyncio.sleep(0)
        for spec in registered:
            cocotb._vpi_event(spec['id'])
    print(json.dumps({'logs': logs, 'registered': registered}))

asyncio.get_event_loop().run_until_complete(main())
`;

describe('cocotb shim', () => {
  it.skipIf(!hasPython())('supports ReadOnly and the cocotb 2.0 unit= keyword', () => {
    const out = execFileSync('python3', ['-c', HARNESS], { input: SHIM, encoding: 'utf8' });
    const { logs, registered } = JSON.parse(out);
    expect(logs).toEqual(['PASS  test_lesson_api']);
    expect(registered.map(({ id, ...spec }) => spec)).toEqual([
      { type: 'timer', fs: 3_000_000 },
      { type: 'timer', fs: 2_000_000 },
      { type: 'read_only' }
    ]);
  });
});
