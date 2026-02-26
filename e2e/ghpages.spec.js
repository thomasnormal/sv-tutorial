/**
 * Smoke tests against the live GitHub Pages deployment.
 * Run with: npx playwright test e2e/ghpages.spec.js
 */
import { test, expect } from '@playwright/test';

const BASE = 'https://thomasnormal.github.io/sv-tutorial';

// ── helpers ──────────────────────────────────────────────────────────────────

async function goToLesson(page, path, heading) {
  await page.goto(`${BASE}${path}`);
  await expect(page.getByRole('heading', { level: 2, name: heading })).toBeVisible({ timeout: 20_000 });
}

async function applySolution(page) {
  await page.getByTestId('options-button').click();
  const btn = page.getByTestId('solve-button');
  await expect(btn).toBeVisible({ timeout: 5_000 });
  const label = ((await btn.textContent()) ?? '').trim();
  if (label !== 'Reset to starter') await btn.click();
  else await page.keyboard.press('Escape');
}

async function expectCleanUvmRun(logs) {
  await expect(logs).toContainText('$ circt-verilog', { timeout: 45_000 });
  await expect(logs).toContainText('--uvm-path /circt/uvm-core', { timeout: 10_000 });
  await expect.poll(
    async () => (await logs.textContent()) ?? '',
    { timeout: 60_000, intervals: [500, 1000] }
  ).toMatch(/\$ circt-sim|runtime unavailable|# circt-verilog exit code: 1/);

  const text = await logs.textContent();
  expect(text).toContain('$ circt-sim');
  expect(text).not.toContain('# circt-verilog exit code: 1');
  expect(text).not.toContain('# circt-sim exit code: 1');
  expect(text).not.toContain('runtime unavailable');
}

// ── tests ─────────────────────────────────────────────────────────────────────

test('site loads and shows lesson content', async ({ page }) => {
  await page.goto(BASE);
  await expect(page.getByRole('heading', { level: 1, name: /System Verilog Tutorial/i })).toBeVisible({ timeout: 20_000 });
  // Sidebar visible
  await expect(page.getByText('SystemVerilog Basics', { exact: true })).toBeVisible();
});

test('UVM: Driver lesson compiles and simulates', async ({ page }) => {
  await goToLesson(page, '/lesson/uvm/driver', 'The Driver');
  await applySolution(page);
  await page.getByTestId('run-button').click();
  await expectCleanUvmRun(page.getByTestId('runtime-logs'));
});

test('UVM: Cross Coverage compiles with intersect syntax', async ({ page }) => {
  await goToLesson(page, '/lesson/uvm/cross-coverage', 'Cross Coverage');
  await applySolution(page);
  await page.getByTestId('run-button').click();
  await expectCleanUvmRun(page.getByTestId('runtime-logs'));
});

test('offline bundle: download completes without error', async ({ page }) => {
  await page.goto(BASE);
  await expect(page.getByRole('heading', { level: 1 })).toBeVisible({ timeout: 20_000 });

  // Find and click the download offline bundle button
  const dlBtn = page.getByTestId('offline-download-button');
  await expect(dlBtn).toBeVisible({ timeout: 10_000 });
  await expect(dlBtn).toBeEnabled();
  await dlBtn.click();

  // Should show progress then "offline ready" — wait up to 3 min for full download
  await expect.poll(
    async () => (await page.getByTestId('offline-download-status').textContent().catch(() => '')) ?? '',
    { timeout: 180_000, intervals: [2000, 5000] }
  ).toMatch(/offline ready|download failed/);

  const statusText = await page.getByTestId('offline-download-status').textContent().catch(() => '');
  expect(statusText).not.toContain('download failed');
});

test('offline mode: lesson runs after service worker caches assets', async ({ page, context }) => {
  await page.goto(BASE);
  await expect(page.getByRole('heading', { level: 1 })).toBeVisible({ timeout: 20_000 });

  // Download bundle first (may already be cached from previous test if same context)
  const dlBtn = page.getByTestId('offline-download-button');
  const isEnabled = await dlBtn.isEnabled().catch(() => false);
  if (isEnabled) {
    await dlBtn.click();
    await expect.poll(
      async () => (await page.getByTestId('offline-download-status').textContent().catch(() => '')) ?? '',
      { timeout: 180_000, intervals: [2000, 5000] }
    ).toMatch(/offline ready|download failed/);
    const st = await page.getByTestId('offline-download-status').textContent().catch(() => '');
    expect(st).not.toContain('download failed');
  }

  // Go offline and verify a lesson still loads
  await context.setOffline(true);
  await page.goto(`${BASE}/lesson/sv/always-ff`);
  await expect(page.getByTestId('lesson-title')).toBeVisible({ timeout: 20_000 });
  await context.setOffline(false);
});
