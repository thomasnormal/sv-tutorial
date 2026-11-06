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
const ENVIRONMENT_BLOCKER = 'browser environment gap; documented in the lesson and coordinator census';
const KNOWN_FAILURES = {
  'sv/events run': `${WASM_REFUSAL}: __moore_event_trigger is unresolved in mox-sim`,
  'sv/fsm run': `${WASM_REFUSAL}: published WASM rejects an unpacked memory variable written by always_ff`,
  'sv/interfaces run': `${WASM_REFUSAL}: __mox_sim_notify_native_memory_write unlinked`,
  'sv/modports run': `${WASM_REFUSAL}: __mox_sim_notify_native_memory_write unlinked`,
  'sv/tasks-functions run': `${WASM_REFUSAL}: continuous-evaluator-effect-ownership-not-admitted`,
  'sv/covergroup-basics run': `${WASM_REFUSAL}: __mox_sim_register_host_allocation`,
  'sv/coverpoint-bins run': `${WASM_REFUSAL}: __mox_sim_register_host_allocation`,
  'sv/cross-coverage run': `${WASM_REFUSAL}: assertMooreCrossBinsofFilterStructABI`,
  'sv/classes run': `${WASM_REFUSAL}: published WASM drops class fields and reports no member named wdata; native Mox passes`,
  'sv/protected-envelope-boundary run': `comment-form protected envelope support is not in the pinned WASM; native Mox passes: ${WASM_REBUILD}`,
  'sv/coverage-option-text run': 'pinned browser WASM lacks the coverage runtime host-allocation linkage; native Mox passes — needs a WASM rebuild',
  'sv/interface-method-receiver run': `interface-method receiver support is newer than the pinned WASM; native Mox passes: ${WASM_REBUILD}`,
  'sva/sequence-basics verify': 'Mox BMC crashes on an assert with a pass action (llhd.process handoff)',
  'sva/formal-assume run': 'Mox evaluates an initial assume property at every clock edge, not once (§16.14.6)',
  'cocotb/edge-triggers run': `${WASM_REFUSAL}: VPI value-change callback did not fire for cocotb edge trigger`,
  'cocotb/clock-and-timing run': `${WASM_REFUSAL}: VPI clock writes did not trigger always_ff edges; counter remained 0 instead of 5`,
  'cocotb/clockcycles-patterns run': `${WASM_REFUSAL}: VPI value-change callback did not fire for cocotb clock cycle trigger`
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
    KNOWN_FAILURES[`${lesson.slug} run`] = `${ENVIRONMENT_BLOCKER}: full-UVM browser compile timed out before simulation`;
  }
}

// The 2026-11-06 published-site matrix showed these formerly-dispositioned
// rows passing on the deployed Mox build. Keep the exact row keys here until
// the next matrix receipt updates the census; an unexpected pass must not make
// the QA suite fail while the reader-facing status is being refreshed.
const PUBLISHED_PASSING = new Set([
  'sv/events run',
  'sv/generate run',
  'sv/covergroup-basics run', 'sv/coverpoint-bins run', 'sv/cross-coverage run',
  'sv/queues-arrays run',
  'sva/vacuous-pass run', 'sva/isunknown run',
  'sva/sequence-basics run', 'sva/sequence-basics verify',
  'sva/implication run', 'sva/implication verify',
  'sva/formal-intro run', 'sva/formal-intro verify',
  'sva/clock-delay run', 'sva/clock-delay verify',
  'sva/rose-fell run', 'sva/rose-fell verify',
  'sva/req-ack run', 'sva/req-ack verify',
  'sva/consecutive-rep run', 'sva/consecutive-rep verify',
  'sva/nonconsec-rep run', 'sva/nonconsec-rep verify',
  'sva/nonconsec-eq run', 'sva/nonconsec-eq verify',
  'sva/throughout run', 'sva/throughout verify',
  'sva/sequence-ops verify',
  'sva/seq-args run', 'sva/seq-args verify',
  'sva/stable-past run', 'sva/stable-past verify',
  'sva/changed run', 'sva/changed verify',
  'sva/disable-iff run', 'sva/disable-iff verify',
  'sva/abort run', 'sva/abort verify',
  'sva/cover-property run', 'sva/cover-property verify',
  'sva/local-vars run', 'sva/local-vars verify',
  'sva/onehot run', 'sva/onehot verify',
  'sva/triggered run', 'sva/triggered verify',
  'sva/checker verify',
  'sva/recursive run', 'sva/recursive verify',
  'sva/bind run', 'sva/let run',
  'sva/formal-assume verify',
  'sva/always-eventually run', 'sva/always-eventually verify',
  'sva/until run', 'sva/until verify',
  'sva/followed-by verify'
]);

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
      test.fail(!!known && !PUBLISHED_PASSING.has(`${lesson.slug} run`), known);
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
      test.fail(!!known && !PUBLISHED_PASSING.has(`${lesson.slug} verify`), known);
      await openSolved(page, lesson);
      expect(await runAndWait(page, 'verify-button')).not.toMatch(FAILURE_RE);
    });
  }
}
