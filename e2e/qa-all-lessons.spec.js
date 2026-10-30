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
const WASM_REFUSAL = 'published Mox WASM refusal; routed to coordinator with the exact construct';
const KNOWN_FAILURES = {
  'sv/events run': `${WASM_REFUSAL}: __moore_event_trigger is unresolved in mox-sim`,
  'sv/interfaces run': `mox-run "memory access out of bounds": ${WASM_REBUILD}`,
  'sv/modports run': `mox-run "memory access out of bounds": ${WASM_REBUILD}`,
  'sv/tasks-functions run': `mox-run "memory access out of bounds": ${WASM_REBUILD}`,
  'sv/covergroup-basics run': `${WASM_REFUSAL}: __mox_sim_register_host_allocation`,
  'sv/coverpoint-bins run': `${WASM_REFUSAL}: __mox_sim_register_host_allocation`,
  'sv/cross-coverage run': `${WASM_REFUSAL}: assertMooreCrossBinsofFilterStructABI`,
  'sv/queues-arrays run': `${WASM_REFUSAL}: __mox_sv_open_array_copy_or_register_bounds`,
  'sv/protected-envelope-boundary run': `comment-form protected envelope support is not in the pinned WASM; native Mox passes: ${WASM_REBUILD}`,
  'sv/coverage-option-text run': 'pinned browser WASM lacks the coverage runtime host-allocation linkage; native Mox passes — needs a WASM rebuild',
  'sv/interface-method-receiver run': `interface-method receiver support is newer than the pinned WASM; native Mox passes: ${WASM_REBUILD}`,
  'sva/sequence-basics verify': 'Mox BMC crashes on an assert with a pass action (llhd.process handoff)',
  'sva/formal-assume run': 'Mox evaluates an initial assume property at every clock edge, not once (§16.14.6)',
  'cocotb/first-test run': `mox-sim-vpi aborts when the simulation starts: ${WASM_REBUILD}`,
  'cocotb/clock-and-timing run': `mox-sim-vpi aborts when the simulation starts: ${WASM_REBUILD}`,
  'cocotb/edge-triggers run': `mox-sim-vpi aborts when the simulation starts: ${WASM_REBUILD}`,
  'cocotb/clockcycles-patterns run': `mox-sim-vpi aborts when the simulation starts: ${WASM_REBUILD}`
};

// The current browser artifact deliberately refuses temporal-property
// evaluation until the Engine 2 evaluator is admitted. Keep every affected
// lesson explicit in the QA report while the source examples remain useful
// documentation and the coordinator tracks the upstream fix.
const SVA_TEMPORAL_REFUSALS = [
  'sva/concurrent-sim', 'sva/vacuous-pass', 'sva/isunknown',
  'sva/sequence-basics', 'sva/implication', 'sva/formal-intro',
  'sva/clock-delay', 'sva/rose-fell', 'sva/req-ack',
  'sva/consecutive-rep', 'sva/nonconsec-rep', 'sva/nonconsec-eq',
  'sva/throughout', 'sva/sequence-ops', 'sva/seq-args',
  'sva/stable-past', 'sva/changed', 'sva/disable-iff', 'sva/abort',
  'sva/cover-property', 'sva/local-vars', 'sva/onehot', 'sva/triggered',
  'sva/checker', 'sva/recursive', 'sva/bind', 'sva/let',
  'sva/formal-assume', 'sva/always-eventually', 'sva/until',
  'sva/followed-by'
];
for (const slug of SVA_TEMPORAL_REFUSALS) {
  const lesson = LESSONS.find((entry) => entry.slug === slug);
  if (!lesson) continue;
  if (['sim', 'both'].includes(lesson.runner)) {
    KNOWN_FAILURES[`${slug} run`] = `${WASM_REFUSAL}: temporal-property-evaluator-not-admitted`;
  }
  if (['bmc', 'lec', 'both'].includes(lesson.runner)) {
    KNOWN_FAILURES[`${slug} verify`] = `${WASM_REFUSAL}: temporal-property-evaluator-not-admitted`;
  }
}
for (const mode of ['run', 'verify']) {
  KNOWN_FAILURES[`sva/nonconsec-rep ${mode}`] = `${WASM_REFUSAL}: goto repetition has an unbounded sampled gap`;
  KNOWN_FAILURES[`sva/nonconsec-eq ${mode}`] = `${WASM_REFUSAL}: sequence-zero-delay-endpoint-overlap-not-representable`;
}
for (const lesson of LESSONS) {
  if (lesson.slug.startsWith('uvm/')) {
    KNOWN_FAILURES[`${lesson.slug} run`] = `mox-verilog Aborted() after UVM/DPI/REGEX: ${WASM_REBUILD}`;
  }
}

// Lessons whose testbench deliberately violates the assertions it teaches.
const EXPECTED_ASSERTION_FAILURES = {
  'sva/concurrent-sim': ['req_gnt_check'],
  'sva/isunknown': ['we_a', 'addr_a', 'rdata_a']
};

async function openSolved(page, lesson) {
  const [part, name] = lesson.slug.split('/');
  await page.goto(`${base}/lesson/${part}/${name}`);
  await expect(page.getByTestId('lesson-title')).toHaveText(lesson.title, { timeout: 10_000 });
  // The title is prerendered; the sidebar's lesson buttons appear only once
  // Svelte has hydrated, and clicks before that are lost.
  await page.locator('button[data-active]').first().waitFor({ timeout: 10_000 });

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
