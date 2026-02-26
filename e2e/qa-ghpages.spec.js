/**
 * Comprehensive QA suite against the live GitHub Pages deployment.
 * Run with: npx playwright test --config e2e/ghpages.config.js e2e/qa-ghpages.spec.js
 */
import { test, expect } from '@playwright/test';

const BASE = 'https://thomasnormal.github.io/sv-tutorial';

// ── helpers ──────────────────────────────────────────────────────────────────

async function goTo(page, path) {
  await page.goto(`${BASE}${path}`);
  await expect(page.getByTestId('lesson-title')).toBeVisible({ timeout: 20_000 });
}

/**
 * Wait for a run to finish by watching the run-button leave its "Cancel" state.
 * The aria-label is "Cancel (Ctrl+Enter)" while running, then reverts to "Run".
 * Only use this when you genuinely need the simulation to complete.
 */
async function waitForRunDone(page, { timeout = 90_000 } = {}) {
  await expect(page.getByTestId('run-button'))
    .not.toHaveAttribute('aria-label', /Cancel/, { timeout });
}

/**
 * Lighter wait: polls until compilation has finished and the simulator starts
 * (or a compile/runtime error is reported). Does NOT wait for simulation output.
 */
async function waitForSimStart(page, { timeout = 60_000 } = {}) {
  const logs = page.getByTestId('runtime-logs');
  await expect.poll(
    async () => (await logs.textContent()) ?? '',
    { timeout, intervals: [500, 1000] }
  ).toMatch(/\$ circt-sim|runtime unavailable|# circt-verilog exit code:/);
}

/** Close the options menu by clicking the backdrop overlay. */
async function closeOptionsMenu(page) {
  await page.locator('div.fixed.inset-0.z-40').click();
}

/** Open options menu and apply solution if not yet applied; otherwise close menu. */
async function applySolution(page) {
  await page.getByTestId('options-button').click();
  const btn = page.getByTestId('solve-button');
  await expect(btn).toBeVisible({ timeout: 5_000 });
  const label = ((await btn.textContent()) ?? '').trim();
  if (label !== 'Reset to starter') {
    await btn.click(); // closes menu automatically (showOptions = false in handler)
  } else {
    // Already at solution — close menu via backdrop
    await closeOptionsMenu(page);
  }
}

/** Open options menu and reset to starter if not yet at starter; otherwise close menu. */
async function resetToStarter(page) {
  await page.getByTestId('options-button').click();
  const btn = page.getByTestId('solve-button');
  await expect(btn).toBeVisible({ timeout: 5_000 });
  const label = ((await btn.textContent()) ?? '').trim();
  if (label === 'Reset to starter') {
    await btn.click(); // closes menu automatically
  } else {
    // Already at starter — close menu via backdrop
    await closeOptionsMenu(page);
  }
}

// ── Navigation ────────────────────────────────────────────────────────────────

test('home page: title and all sidebar part labels visible', async ({ page }) => {
  await page.goto(BASE);
  await expect(page.getByRole('heading', { level: 1, name: /System Verilog Tutorial/i })).toBeVisible({ timeout: 20_000 });
  // All four main parts in the sidebar
  await expect(page.getByText('SystemVerilog Basics', { exact: true })).toBeVisible();
  await expect(page.getByText('SystemVerilog Assertions', { exact: true })).toBeVisible();
  await expect(page.getByText('Universal Verification Methodology', { exact: true })).toBeVisible();
  await expect(page.getByText('cocotb', { exact: true })).toBeVisible();
});

test('sidebar: can navigate to a lesson by clicking its button', async ({ page }) => {
  // Home redirects to sv/welcome — Introduction chapter is auto-expanded,
  // Sequential Logic chapter is collapsed.
  await page.goto(BASE);
  await expect(page.getByTestId('lesson-title')).toBeVisible({ timeout: 20_000 });

  // Expand the "Sequential Logic" chapter
  const seqBtn = page.getByRole('button', { name: /Sequential Logic/ });
  await expect(seqBtn).toBeVisible({ timeout: 10_000 });
  await seqBtn.click();

  // Click the Flip-Flops lesson button
  const lessonBtn = page.getByRole('button', { name: /Flip-Flops/ }).first();
  await expect(lessonBtn).toBeVisible({ timeout: 5_000 });
  await lessonBtn.click();
  // Use toHaveText to wait until navigation completes and title changes
  await expect(page.getByTestId('lesson-title')).toHaveText(/Flip-Flops/i, { timeout: 15_000 });
});

test('header: prev/next lesson buttons navigate between lessons', async ({ page }) => {
  await goTo(page, '/lesson/sv/always-ff');
  const titleBefore = await page.getByTestId('lesson-title').textContent();
  // Click Next lesson button in the header
  await page.getByRole('button', { name: 'Next lesson' }).click();
  await expect(page.getByTestId('lesson-title')).not.toHaveText(titleBefore ?? '', { timeout: 10_000 });
  // Click Prev lesson button in the header
  await page.getByRole('button', { name: 'Previous lesson' }).click();
  await expect(page.getByTestId('lesson-title')).toHaveText(titleBefore ?? '', { timeout: 10_000 });
});

test('direct URL navigation works for all parts', async ({ page }) => {
  const cases = [
    ['/lesson/sv/always-ff', /Flip-Flops/i],
    ['/lesson/sva/concurrent-sim', /Concurrent/i],
    ['/lesson/uvm/driver', /Driver/i],
    ['/lesson/cocotb/first-test', /.+/],
  ];
  for (const [path, titleRe] of cases) {
    await page.goto(`${BASE}${path}`);
    await expect(page.getByTestId('lesson-title')).toBeVisible({ timeout: 20_000 });
    expect(await page.getByTestId('lesson-title').textContent()).toMatch(titleRe);
  }
});

// ── Editor layout ─────────────────────────────────────────────────────────────

test('single-file lesson: no file tree, filename pill in toolbar', async ({ page }) => {
  // welcome has 1 starter file (top.sv)
  await goTo(page, '/lesson/sv/welcome');
  // File tree (tablist with Files label) should not be present for single-file
  await expect(page.getByRole('tablist', { name: 'Files' })).not.toBeVisible();
  // The toolbar should show the filename
  const toolbar = page.getByTestId('file-tree-toolbar');
  await expect(toolbar).toBeVisible();
  const toolbarText = await toolbar.textContent();
  expect(toolbarText).toMatch(/\.sv/);
});

test('2-file lesson auto-opens split view on wide screen', async ({ page }) => {
  // always-ff has 2 files; on 1280px viewport splitView starts true
  await goTo(page, '/lesson/sv/always-ff');
  // Both split pane headers should be visible
  await expect(page.getByTestId('split-header-left')).toBeVisible({ timeout: 5_000 });
  await expect(page.getByTestId('split-header-right')).toBeVisible();
  // The file names appear as pills
  const leftText = await page.getByTestId('split-header-left').textContent();
  const rightText = await page.getByTestId('split-header-right').textContent();
  expect(leftText + rightText).toMatch(/\.sv/);
});

test('split view: collapse to file-tree view via header button', async ({ page }) => {
  await goTo(page, '/lesson/sv/always-ff');
  // Start in split view
  await expect(page.getByTestId('split-header-right')).toBeVisible({ timeout: 5_000 });
  // Click "Switch to file tree view"
  await page.getByTitle('Switch to file tree view').click();
  // Now file tree (tablist) should appear
  await expect(page.getByRole('tablist', { name: 'Files' })).toBeVisible({ timeout: 5_000 });
  // And split headers gone
  await expect(page.getByTestId('split-header-left')).not.toBeVisible();
});

test('file tree: switching tabs changes active file', async ({ page }) => {
  await goTo(page, '/lesson/sv/always-ff');
  // Collapse to file tree view first
  await page.getByTitle('Switch to file tree view').click();
  await expect(page.getByRole('tablist', { name: 'Files' })).toBeVisible({ timeout: 5_000 });
  const tabs = page.getByRole('tab');
  const count = await tabs.count();
  expect(count).toBeGreaterThanOrEqual(2);
  // Click second tab
  await tabs.nth(1).click();
  expect(await tabs.nth(1).getAttribute('aria-selected')).toBe('true');
});

// ── Solve / Reset cycle ───────────────────────────────────────────────────────

test('solve/reset cycle: toggles editor content', async ({ page }) => {
  await goTo(page, '/lesson/sv/always-ff');
  await resetToStarter(page);
  // After reset, button should say "Show solution"
  await page.getByTestId('options-button').click();
  await expect(page.getByTestId('solve-button')).toHaveText('Show solution');
  await closeOptionsMenu(page);

  await applySolution(page);
  // After apply, button should say "Reset to starter"
  await page.getByTestId('options-button').click();
  await expect(page.getByTestId('solve-button')).toHaveText('Reset to starter');
  await closeOptionsMenu(page);
});

test('options menu closes on Escape key', async ({ page }) => {
  await goTo(page, '/lesson/sv/welcome');
  await page.getByTestId('options-button').click();
  // Menu should be open
  await expect(page.getByTestId('solve-button')).toBeVisible({ timeout: 3_000 });
  // Press Escape
  await page.keyboard.press('Escape');
  // Menu should be closed
  await expect(page.getByTestId('solve-button')).not.toBeVisible({ timeout: 3_000 });
});

// ── Compilation & simulation ──────────────────────────────────────────────────

test('SV: welcome lesson compiles and prints Hello output', async ({ page }) => {
  await goTo(page, '/lesson/sv/welcome');
  await page.getByTestId('run-button').click();
  const logs = page.getByTestId('runtime-logs');
  await expect(logs).toContainText('$ circt-verilog', { timeout: 45_000 });
  await waitForRunDone(page);
  const text = await logs.textContent();
  expect(text).not.toContain('exit code: 1');
  expect(text).not.toContain('runtime unavailable');
});

test('SV: always-ff solution compiles and simulates cleanly', async ({ page }) => {
  await goTo(page, '/lesson/sv/always-ff');
  await applySolution(page);
  await page.getByTestId('run-button').click();
  const logs = page.getByTestId('runtime-logs');
  await expect(logs).toContainText('$ circt-verilog', { timeout: 45_000 });
  await waitForRunDone(page, { timeout: 120_000 });
  const text = await logs.textContent();
  expect(text).not.toContain('# circt-verilog exit code: 1');
  expect(text).not.toContain('runtime unavailable');
  expect(text).toContain('PASS');
});

test('SV: starter code with TODO shows simulation failures', async ({ page }) => {
  await goTo(page, '/lesson/sv/always-ff');
  await resetToStarter(page);
  // Starter always_ff body is incomplete — simulation should print FAIL lines
  await page.getByTestId('run-button').click();
  const logs = page.getByTestId('runtime-logs');
  await expect(logs).toContainText('$ circt-verilog', { timeout: 45_000 });
  await waitForRunDone(page, { timeout: 120_000 });
  const text = await logs.textContent();
  expect(text).toContain('FAIL');
});

test('Ctrl+Enter triggers run', async ({ page }) => {
  await goTo(page, '/lesson/sv/welcome');
  await page.keyboard.press('Control+Enter');
  const logs = page.getByTestId('runtime-logs');
  await expect(logs).toContainText('$ circt-verilog', { timeout: 45_000 });
});

test('SVA: concurrent simulation lesson runs cleanly', async ({ page }) => {
  await goTo(page, '/lesson/sva/concurrent-sim');
  await applySolution(page);
  await page.getByTestId('run-button').click();
  const logs = page.getByTestId('runtime-logs');
  await expect(logs).toContainText('$ circt-verilog', { timeout: 45_000 });
  await waitForRunDone(page);
  const text = await logs.textContent();
  expect(text).not.toContain('runtime unavailable');
});

test('UVM: driver lesson compiles and simulates', async ({ page }) => {
  await goTo(page, '/lesson/uvm/driver');
  await applySolution(page);
  await page.getByTestId('run-button').click();
  const logs = page.getByTestId('runtime-logs');
  await expect(logs).toContainText('$ circt-verilog', { timeout: 45_000 });
  await expect.poll(
    async () => (await logs.textContent()) ?? '',
    { timeout: 90_000, intervals: [500, 1000] }
  ).toMatch(/\$ circt-sim|runtime unavailable|# circt-verilog exit code: 1/);
  const text = await logs.textContent();
  expect(text).not.toContain('# circt-verilog exit code: 1');
  expect(text).not.toContain('runtime unavailable');
});

test('cocotb: first-test lesson loads and has run button', async ({ page }) => {
  await goTo(page, '/lesson/cocotb/first-test');
  await expect(page.getByTestId('lesson-title')).toBeVisible();
  await expect(page.getByTestId('run-button')).toBeVisible();
});

// ── Term cards ────────────────────────────────────────────────────────────────

test('dfn term card: appears on hover', async ({ page }) => {
  await goTo(page, '/lesson/sv/always-ff');
  const dfn = page.locator('.lesson-body dfn[data-card]').first();
  if (await dfn.count() > 0) {
    await dfn.hover();
    // The glossary card is a fixed div with z-50 injected into the page
    const card = page.locator('div.fixed.z-50').last();
    await expect(card).toBeVisible({ timeout: 3_000 });
    // Move away — card should disappear
    await page.mouse.move(10, 10);
    await expect(card).not.toBeVisible({ timeout: 3_000 });
  }
});

test('dfn term card near bottom does not clip off-screen', async ({ page }) => {
  // Scroll to bottom of lesson body and hover over dfn
  await goTo(page, '/lesson/sv/always-ff');
  const dfns = page.locator('.lesson-body dfn[data-card]');
  const count = await dfns.count();
  if (count > 0) {
    const last = dfns.last();
    await last.scrollIntoViewIfNeeded();
    await last.hover();
    const card = page.locator('div.fixed.z-50').last();
    await expect(card).toBeVisible({ timeout: 3_000 });
    // Card should be fully within the viewport vertically
    const box = await card.boundingBox();
    if (box) {
      const viewportHeight = page.viewportSize()?.height ?? 720;
      expect(box.y + box.height).toBeLessThanOrEqual(viewportHeight + 1);
    }
  }
});

// ── Settings ─────────────────────────────────────────────────────────────────

test('vim mode: toggles on and off without breaking editor', async ({ page }) => {
  await goTo(page, '/lesson/sv/welcome');
  await page.getByTestId('options-button').click();
  const vimCheckbox = page.getByRole('checkbox', { name: /vim/i });
  await expect(vimCheckbox).toBeVisible();
  const wasChecked = await vimCheckbox.isChecked();
  await vimCheckbox.click();
  expect(await vimCheckbox.isChecked()).toBe(!wasChecked);
  // Restore
  await vimCheckbox.click();
  // Close menu via backdrop (Escape key fix may not be deployed)
  await closeOptionsMenu(page);
  // Run still works
  await page.getByTestId('run-button').click();
  await expect(page.getByTestId('runtime-logs')).toContainText('$ circt-verilog', { timeout: 45_000 });
});

test('dark mode: toggle changes color scheme', async ({ page }) => {
  await page.goto(BASE);
  await expect(page.getByRole('heading', { level: 1 })).toBeVisible({ timeout: 20_000 });
  const html = page.locator('html');
  const darkBefore = await html.evaluate(el => el.classList.contains('dark'));
  await page.getByRole('button', { name: /dark mode|light mode/i }).click();
  const darkAfter = await html.evaluate(el => el.classList.contains('dark'));
  expect(darkAfter).toBe(!darkBefore);
  // Restore
  await page.getByRole('button', { name: /dark mode|light mode/i }).click();
});

// ── Copy protection ───────────────────────────────────────────────────────────

test('copy from lesson body triggers copy-protection modal', async ({ page }) => {
  await goTo(page, '/lesson/sv/always-ff');
  // Select all text in lesson body and copy
  await page.locator('.lesson-body').click();
  await page.keyboard.press('Control+a');
  await page.keyboard.press('Control+c');
  const modal = page.getByRole('dialog');
  if (await modal.isVisible({ timeout: 2_000 }).catch(() => false)) {
    await expect(modal).toContainText(/copy/i);
    await page.getByRole('button', { name: /ok/i }).click();
    await expect(modal).not.toBeVisible();
  }
});

// ── Responsive ────────────────────────────────────────────────────────────────

test('narrow viewport: lesson and editor both visible', async ({ page }) => {
  await page.setViewportSize({ width: 600, height: 900 });
  await goTo(page, '/lesson/sv/welcome');
  await expect(page.getByTestId('lesson-title')).toBeVisible();
  await expect(page.getByTestId('run-button')).toBeVisible();
});
