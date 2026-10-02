import { test, expect } from '@playwright/test';

const EXPECTED_TOOLBAR_HEIGHT = 40; // h-10 = 2.5rem = 40px at default font size

test.describe('Split view header pills', () => {
  test('both file pills are compact and both bars are the same height', async ({ page }) => {
    // modules-and-ports has two source files (adder.sv + tb.sv) — auto-opens in split view
    await page.goto('/lesson/sv/modules-and-ports', { waitUntil: 'networkidle' });

    const headerLeft  = page.getByTestId('split-header-left');
    const headerRight = page.getByTestId('split-header-right');

    await expect(headerLeft).toBeVisible();
    await expect(headerRight).toBeVisible();

    const boxLeft  = await headerLeft.boundingBox();
    const boxRight = await headerRight.boundingBox();

    console.log(`left  bar: ${Math.round(boxLeft.width)}×${Math.round(boxLeft.height)}px`);
    console.log(`right bar: ${Math.round(boxRight.width)}×${Math.round(boxRight.height)}px`);

    // Both header bars must be the same height
    expect(boxLeft.height).toBeCloseTo(boxRight.height, 0);

    // The file name pills inside each bar must be compact (not stretched to pane width)
    const pillA = headerLeft.locator('span');
    const pillB = headerRight.locator('span').first();

    const wA = (await pillA.boundingBox()).width;
    const wB = (await pillB.boundingBox()).width;

    console.log(`fileA pill width: ${Math.round(wA)}px`);
    console.log(`fileB pill width: ${Math.round(wB)}px`);

    // Pills should be text-sized, not pane-width (~640px for 50/50 split)
    expect(wA).toBeLessThan(300);
    expect(wB).toBeLessThan(300);
  });

  test('editing either split pane clears a completed solution', async ({ page }) => {
    await page.goto('/lesson/sv/modules-and-ports', { waitUntil: 'networkidle' });

    await page.getByTestId('options-button').first().click();
    await page.getByTestId('solve-button').first().click();
    await page.getByTestId('run-button').first().click();
    await expect(page.getByTestId('runtime-logs')).toContainText('PASS', { timeout: 120_000 });

    await page.getByTestId('options-button').first().click();
    await expect(page.getByTestId('solve-button').first()).toHaveText('Reset to starter');
    await page.keyboard.press('Escape');

    const rightEditor = page.locator('[aria-label="Code editor: /src/tb.sv"]');
    await rightEditor.click();
    await page.keyboard.press('End');
    await page.keyboard.type(' ');

    await page.getByTestId('options-button').first().click();
    await expect(page.getByTestId('solve-button').first()).toHaveText('Show solution');
  });

  test('editing during a run cannot restore completion for the old source', async ({ page }) => {
    await page.goto('/lesson/sv/modules-and-ports', { waitUntil: 'networkidle' });

    await page.getByTestId('options-button').first().click();
    await page.getByTestId('solve-button').first().click();
    const runButton = page.getByTestId('run-button').first();
    await runButton.click();
    await expect(runButton).toHaveAttribute('aria-label', 'Cancel (Ctrl+Enter)', { timeout: 120_000 });

    const rightEditor = page.locator('[aria-label="Code editor: /src/tb.sv"]');
    await rightEditor.click();
    await page.keyboard.press('End');
    await page.keyboard.type(' ');

    await expect(runButton).not.toHaveAttribute('aria-label', 'Cancel (Ctrl+Enter)', { timeout: 120_000 });
    await page.getByTestId('options-button').first().click();
    await expect(page.getByTestId('solve-button').first()).toHaveText('Show solution');
  });
});

test.describe('Toolbar height consistency', () => {
  test('file-tree toolbar and split-view headers are the same height', async ({ page }) => {
    // 1. File-tree mode: open a multi-file lesson (uvm/driver has 6+ files, never splits)
    await page.goto('/lesson/uvm/driver', { waitUntil: 'networkidle' });

    const treeToolbar = page.getByTestId('file-tree-toolbar');
    await expect(treeToolbar).toBeVisible();

    const treeBox = await treeToolbar.boundingBox();
    console.log(`file-tree toolbar height: ${Math.round(treeBox.height)}px`);
    expect(treeBox.height).toBeCloseTo(EXPECTED_TOOLBAR_HEIGHT, 0);

    // 2. Split-view mode: open a 2-file lesson and activate split view
    await page.goto('/lesson/sv/modules-and-ports', { waitUntil: 'networkidle' });

    const splitLeft  = page.getByTestId('split-header-left');
    const splitRight = page.getByTestId('split-header-right');
    await expect(splitLeft).toBeVisible();
    await expect(splitRight).toBeVisible();

    const splitLeftBox  = await splitLeft.boundingBox();
    const splitRightBox = await splitRight.boundingBox();
    console.log(`split-header-left  height: ${Math.round(splitLeftBox.height)}px`);
    console.log(`split-header-right height: ${Math.round(splitRightBox.height)}px`);

    expect(splitLeftBox.height).toBeCloseTo(EXPECTED_TOOLBAR_HEIGHT, 0);
    expect(splitRightBox.height).toBeCloseTo(EXPECTED_TOOLBAR_HEIGHT, 0);
  });

  test('file-tree toolbar and split-view headers both have a bottom border', async ({ page }) => {
    // File-tree mode
    await page.goto('/lesson/uvm/driver', { waitUntil: 'networkidle' });
    const treeToolbar = page.getByTestId('file-tree-toolbar');
    await expect(treeToolbar).toBeVisible();
    const treeBorderBottom = await treeToolbar.evaluate(
      el => getComputedStyle(el).borderBottomWidth
    );
    expect(treeBorderBottom).not.toBe('0px');

    // Split-view mode
    await page.goto('/lesson/sv/modules-and-ports', { waitUntil: 'networkidle' });
    const splitRight = page.getByTestId('split-header-right');
    await expect(splitRight).toBeVisible();
    const splitBorderBottom = await splitRight.evaluate(
      el => getComputedStyle(el).borderBottomWidth
    );
    expect(splitBorderBottom).not.toBe('0px');
  });
});
