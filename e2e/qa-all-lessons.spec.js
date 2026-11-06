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
const WASM_REFUSAL = 'published Mox WASM refusal; routed to coordinator with the exact construct';
const ENVIRONMENT_BLOCKER = 'browser environment gap; documented in the lesson and coordinator census';
const KNOWN_FAILURES = {
  'sv/fsm run': `${WASM_REFUSAL}: published WASM rejects an unpacked memory variable written by always_ff`,
  'sv/interfaces run': `${WASM_REFUSAL}: __mox_sim_notify_native_memory_write unlinked`,
  'sv/modports run': `${WASM_REFUSAL}: __mox_sim_notify_native_memory_write unlinked`,
  'sv/tasks-functions run': `${WASM_REFUSAL}: continuous-evaluator-effect-ownership-not-admitted`,
  'sv/classes run': `${WASM_REFUSAL}: published WASM drops class fields and reports no member named wdata; native Mox passes`,
  'cocotb/edge-triggers run': `${WASM_REFUSAL}: VPI value-change callback did not fire for cocotb edge trigger`,
  'cocotb/clock-and-timing run': `${WASM_REFUSAL}: VPI clock writes did not trigger always_ff edges; counter remained 0 instead of 5`,
  'cocotb/clockcycles-patterns run': `${WASM_REFUSAL}: VPI value-change callback did not fire for cocotb clock cycle trigger`
};

// The current browser artifact deliberately refuses temporal-property
// evaluation for only the rows that still fail in the latest published matrix.
// Rows that now pass are ordinary tests again, so a later regression cannot be
// hidden by an obsolete expected-failure marker.
for (const key of [
  'sva/concurrent-sim run',
  'sva/immediate-assert run', 'sva/immediate-assert verify',
  'sva/sequence-ops run',
  'sva/checker run',
  'sva/formal-assume run',
  'sva/lec verify',
  'sva/followed-by verify'
]) {
  KNOWN_FAILURES[key] = `${WASM_REFUSAL}: temporal-property-evaluator-not-admitted`;
}
for (const lesson of LESSONS) {
  if (lesson.slug.startsWith('uvm/')) {
    KNOWN_FAILURES[`${lesson.slug} run`] = `${ENVIRONMENT_BLOCKER}: full-UVM browser compile timed out before simulation`;
  }
}

// Lessons whose testbench deliberately violates the assertions it teaches.
const EXPECTED_ASSERTION_FAILURES = {
  'sva/concurrent-sim': ['req_gnt_check'],
  'sva/isunknown': ['we_a', 'addr_a', 'rdata_a']
};

async function openSolved(page, lesson) {
  const [part, name] = lesson.slug.split('/');
  const route = `lesson/${part}/${name}`;
  await page.goto(base ? `${base}/${route}` : route);
  await expect(page.getByTestId('lesson-title')).toHaveText(lesson.title, { timeout: 10_000 });
  // The title is prerendered; the sidebar's lesson buttons appear only once
  // Svelte has hydrated, and clicks before that are lost.
  await page.getByTestId('options-button').waitFor({ timeout: 10_000 });

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
