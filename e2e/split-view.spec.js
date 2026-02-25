import { test, expect } from '@playwright/test';

test.describe('Split view header pills', () => {
  test('both file pills are compact and both bars are the same height', async ({ page }) => {
    // priority-enc has two files (priority_enc.sv + tb.sv) — auto-opens in split view
    await page.goto('/lesson/sv/priority-enc', { waitUntil: 'networkidle' });

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
});
