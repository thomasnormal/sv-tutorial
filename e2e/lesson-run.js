/**
 * Shared helpers for the whole-tutorial e2e specs.
 *
 * The lesson list is derived from src/lessons/meta.js (the single source of
 * truth), so renamed or added lessons can't silently drop out of coverage.
 */
import { readdirSync, readFileSync } from 'node:fs';
import { expect } from '@playwright/test';
import meta from '../src/lessons/meta.js';

const LESSONS_DIR = new URL('../src/lessons/', import.meta.url);

/** Solution files of a lesson: starters with each `x.sol.sv` replacing `x.sv`. */
function solutionSources(slug) {
  const dir = new URL(`${slug}/`, LESSONS_DIR);
  const files = {};
  for (const name of readdirSync(dir)) {
    if (!/\.(sv|mlir)$/.test(name)) continue;
    const key = name.replace(/\.sol\./, '.');
    if (name.includes('.sol.') || !(key in files)) files[key] = readFileSync(new URL(name, dir), 'utf8');
  }
  return Object.values(files);
}

export const LESSONS = Object.entries(meta).map(([slug, m]) => ({
  slug,
  title: m.title,
  runner: m.runner ?? 'sim',
  // The solution reports its own verdict, so a finished run must say PASS.
  printsPass: solutionSources(slug).some((src) => /"[^"\n]*\bPASS\b/.test(src))
}));

// Anything in the log that means a tool (or the runtime) failed.
export const FAILURE_RE = /exit code: [1-9]|Aborted\(|runtime unavailable/;
// The runtime itself broke (as opposed to the design reporting failures).
export const CRASH_RE = /Aborted\(|runtime unavailable/;
// A cocotb test failed, or the Python test file raised (e.g. ImportError).
export const COCOTB_FAILURE_RE = /^(FAIL|ERROR)\s|\w+Error\b/m;

// Below the 180 s test timeout, so a hung run fails an assertion (which
// test.fail can expect) instead of timing out the test.
const RUN_TIMEOUT = 150_000;

/**
 * Click a run/verify button and wait until that run has finished: the log
 * is cleared at start, so a "$ mox" line means this run began, and the button
 * leaves its "Cancel" state only when the run returns.
 */
export async function runAndWait(page, testId) {
  const button = page.getByTestId(testId);
  const logs = page.getByTestId('runtime-logs');
  const deadline = Date.now() + RUN_TIMEOUT;
  const remaining = () => Math.max(1, deadline - Date.now());
  await button.click();
  await expect(logs).toContainText('$ mox', { timeout: remaining() });
  await expect(button).not.toHaveAttribute('aria-label', /^Cancel/, { timeout: remaining() });
  return logs.innerText();
}
