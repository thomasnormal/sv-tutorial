/**
 * Mobile navigation drawer tests.
 * Tests the overlay drawer (shadcn Sidebar) that appears in narrow mode (<980px).
 */
import { test, expect } from '@playwright/test';

const NARROW = { width: 600, height: 900 };
const WIDE   = { width: 1280, height: 800 };

test.describe('mobile nav drawer', () => {
  test('sidebar is hidden in narrow mode initially', async ({ page }) => {
    await page.setViewportSize(NARROW);
    await page.goto('/');
    // No drawer open on load
    await expect(page.getByRole('dialog')).not.toBeVisible();
  });

  test('sidebar trigger button opens the drawer in narrow mode', async ({ page }) => {
    await page.setViewportSize(NARROW);
    await page.goto('/');

    await page.getByRole('button', { name: /toggle sidebar/i }).click();

    // Drawer dialog should now be visible
    const dialog = page.getByRole('dialog');
    await expect(dialog).toBeVisible();

    // Lesson buttons are accessible inside the drawer (scope to dialog to avoid ambiguity)
    await expect(dialog.getByRole('button', { name: /Welcome/ })).toBeVisible();
  });

  test('clicking a lesson inside the drawer navigates', async ({ page }) => {
    await page.setViewportSize(NARROW);
    await page.goto('/');

    // Open the drawer
    await page.getByRole('button', { name: /toggle sidebar/i }).click();
    const dialog = page.getByRole('dialog');
    await expect(dialog).toBeVisible();

    // "Introduction" chapter is auto-expanded; click "Modules and Ports" scoped to dialog
    await dialog.getByRole('button', { name: /Modules and Ports/i }).click();

    // Page navigated
    await expect(page.getByTestId('lesson-title')).toHaveText('Modules and Ports', { timeout: 10_000 });
  });

  test('desktop sidebar has nav buttons visible', async ({ page }) => {
    await page.setViewportSize(WIDE);
    await page.goto('/');
    // The inner sidebar container should be in the DOM and visible
    const sidebar = page.locator('[data-sidebar="sidebar"]');
    await expect(sidebar).toBeVisible();
    // Chapter buttons are accessible directly (not in a dialog)
    await expect(page.locator('[data-sidebar="sidebar"]').getByRole('button', { name: 'Introduction' })).toBeVisible();
  });

  test('desktop sidebar toggle collapses and restores the panel', async ({ page }) => {
    await page.setViewportSize(WIDE);
    await page.goto('/');

    const gap = page.locator('[data-slot="sidebar-gap"]');
    // Sidebar starts expanded — gap has a non-zero width
    const initialWidth = await gap.evaluate(el => el.getBoundingClientRect().width);
    expect(initialWidth).toBeGreaterThan(0);

    // Toggle collapses (200ms transition — wait for it)
    await page.getByRole('button', { name: /toggle sidebar/i }).click();
    await page.waitForTimeout(300);
    const collapsedWidth = await gap.evaluate(el => el.getBoundingClientRect().width);
    expect(collapsedWidth).toBe(0);

    // Toggle restores
    await page.getByRole('button', { name: /toggle sidebar/i }).click();
    await page.waitForTimeout(300); // allow transition
    const restoredWidth = await gap.evaluate(el => el.getBoundingClientRect().width);
    expect(restoredWidth).toBeGreaterThan(0);
  });
});
