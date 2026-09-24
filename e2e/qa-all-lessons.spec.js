/**
 * Full-tutorial QA: every lesson → solve → run/verify → no errors.
 * Lessons are visited by their slug URL (/lesson/part/name) for reliable navigation.
 * Simulation (Run) and formal (Verify) are separate tests so a failure in one
 * does not hide the other.
 */
import { test, expect } from '@playwright/test';
import { LESSONS, FAILURE_RE, CRASH_RE, COCOTB_FAILURE_RE, runAndWait } from './lesson-run.js';

const base = process.env.VITE_BASE?.replace(/\/$/, '') ?? '';

// Solutions that are known not to pass yet, keyed by `slug run|verify`. Each
// entry names its cause; once fixed, Playwright reports the test as
// "unexpectedly passed" so the entry gets removed.
const WASM_REBUILD = 'pinned mox WASM (805b42d2) bug; native Mox passes — needs a WASM rebuild';
const KNOWN_FAILURES = {
  'sv/interfaces run': `mox-run "memory access out of bounds": ${WASM_REBUILD}`,
  'sv/modports run': `mox-run "memory access out of bounds": ${WASM_REBUILD}`,
  'sv/tasks-functions run': `mox-run "memory access out of bounds": ${WASM_REBUILD}`,
  'sv/fsm run': `false "mem driven by always_ff" error on sram.sv: ${WASM_REBUILD}`,
  'sva/sequence-basics verify': 'Mox BMC crashes on an assert with a pass action (llhd.process handoff)',
  'sv/queues-arrays run': 'static initializer in the pop loop runs once (§6.21), so the loop never ends',
  'sv/randomization run': 'hard low_bank_c conflicts with the inline high-bank constraint (§18.7)',
  'sva/formal-assume run': "assume on the design's state fails at the first edge (state is X)",
  'mlir/intro run': 'Run simulates the design module, not the @tb testbench, so no PASS is printed',
  'mlir/comb run': 'Run simulates the design module, not the @tb testbench, so no PASS is printed',
  'mlir/seq run': 'Run simulates the design module, not the @tb testbench',
  'mlir/lowering run': 'Run simulates the design module, not the @tb testbench',
  'cocotb/first-test run': `mox-sim-vpi aborts when the simulation starts: ${WASM_REBUILD}`,
  'cocotb/clock-and-timing run': `mox-sim-vpi aborts when the simulation starts: ${WASM_REBUILD}`,
  'cocotb/edge-triggers run': `mox-sim-vpi aborts when the simulation starts: ${WASM_REBUILD}`,
  'cocotb/clockcycles-patterns run': `mox-sim-vpi aborts when the simulation starts: ${WASM_REBUILD}`
};
for (const lesson of LESSONS) {
  if (lesson.slug.startsWith('uvm/')) {
    KNOWN_FAILURES[`${lesson.slug} run`] = `mox-verilog Aborted() after UVM/DPI/REGEX: ${WASM_REBUILD}`;
  }
}

// Lessons whose testbench deliberately violates the assertions it teaches.
const EXPECTED_ASSERTION_FAILURES = {
  'sva/isunknown': ['we_a', 'addr_a', 'rdata_a']
};

async function openSolved(page, lesson) {
  const [part, name] = lesson.slug.split('/');
  await page.goto(`${base}/lesson/${part}/${name}`);
  await expect(page.getByTestId('lesson-title')).toHaveText(lesson.title, { timeout: 10_000 });

  await page.getByTestId('options-button').click();
  const solveBtn = page.getByTestId('solve-button');
  if (await solveBtn.count() > 0) {
    const label = ((await solveBtn.textContent()) ?? '').trim();
    if (label !== 'Reset to starter') await solveBtn.click();
    else await page.keyboard.press('Escape');
  } else {
    await page.keyboard.press('Escape');
  }
}

for (const [index, lesson] of LESSONS.entries()) {
  const name = `[${String(index + 1).padStart(2)}] ${lesson.title}`;
  const runs = ['sim', 'cocotb', 'both'].includes(lesson.runner);
  const verifies = ['bmc', 'lec', 'both'].includes(lesson.runner);

  if (runs) {
    test(`${name} › run`, async ({ page }) => {
      const known = KNOWN_FAILURES[`${lesson.slug} run`];
      test.fail(!!known, known);
      await openSolved(page, lesson);
      const log = await runAndWait(page, 'run-button');
      const expectedFailures = EXPECTED_ASSERTION_FAILURES[lesson.slug];
      if (expectedFailures) {
        expect(log).not.toMatch(CRASH_RE);
        for (const label of expectedFailures) expect(log).toContain(`SVA assertion failed: ${label}`);
      } else if (lesson.runner === 'cocotb') {
        // The cocotb shim reports one `PASS  name` / `FAIL  name` line per test.
        expect(log).toMatch(/^PASS\s+\w+/m);
        expect(log).not.toMatch(COCOTB_FAILURE_RE);
      } else {
        expect(log).not.toMatch(FAILURE_RE);
        if (lesson.printsPass) expect(log).toMatch(/\bPASS\b/);
      }
    });
  }

  if (verifies) {
    test(`${name} › verify`, async ({ page }) => {
      const known = KNOWN_FAILURES[`${lesson.slug} verify`];
      test.fail(!!known, known);
      await openSolved(page, lesson);
      expect(await runAndWait(page, 'verify-button')).not.toMatch(FAILURE_RE);
    });
  }
}
