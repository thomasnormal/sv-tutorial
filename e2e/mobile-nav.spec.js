/**
 * Sidebar navigation tests.
 * The sidebar uses a panel+gap approach on all screen sizes (no Sheet overlay).
 * On narrow screens (<980px) it starts collapsed; on wide screens it starts expanded.
 */
import { test, expect } from '@playwright/test';

const NARROW = { width: 600, height: 900 };
const WIDE   = { width: 1280, height: 800 };

test.describe('sidebar navigation', () => {
  // Waits for the sidebar gap transition to settle at width 0 (collapsed)
  async function waitForCollapsed(page) {
    await page.waitForFunction(() => {
      const el = document.querySelector('[data-slot="sidebar-gap"]');
      return el && el.getBoundingClientRect().width < 1;
    }, { timeout: 5000 });
  }

  // Waits for the sidebar gap transition to settle at width > 0 (expanded)
  async function waitForExpanded(page) {
    await page.waitForFunction(() => {
      const el = document.querySelector('[data-slot="sidebar-gap"]');
      return el && el.getBoundingClientRect().width > 0;
    }, { timeout: 5000 });
  }

  test('sidebar starts collapsed in narrow mode', async ({ page }) => {
    await page.setViewportSize(NARROW);
    await page.goto('/');
    // onMount closes the sidebar on narrow viewports; wait for transition to complete
    await waitForCollapsed(page);
    const gap = page.locator('[data-slot="sidebar-gap"]');
    const width = await gap.evaluate(el => el.getBoundingClientRect().width);
    expect(width).toBe(0);
  });

  test('sidebar trigger opens the panel in narrow mode', async ({ page }) => {
    await page.setViewportSize(NARROW);
    await page.goto('/');
    // Wait for onMount to close the sidebar first
    await waitForCollapsed(page);

    await page.getByRole('button', { name: /toggle sidebar/i }).click();
    // Wait for the open transition to settle
    await waitForExpanded(page);

    const gap = page.locator('[data-slot="sidebar-gap"]');
    const width = await gap.evaluate(el => el.getBoundingClientRect().width);
    expect(width).toBeGreaterThan(0);

    // Nav buttons are accessible inside the sidebar panel
    const sidebar = page.locator('[data-sidebar="sidebar"]');
    await expect(sidebar.getByRole('button', { name: /Welcome/ })).toBeVisible();
  });

  test('clicking a lesson inside the panel navigates', async ({ page }) => {
    await page.setViewportSize(NARROW);
    await page.goto('/');

    // Open the sidebar
    await page.getByRole('button', { name: /toggle sidebar/i }).click();
    await page.waitForTimeout(300);

    // "Introduction" chapter is auto-expanded; click "Modules and Ports"
    const sidebar = page.locator('[data-sidebar="sidebar"]');
    await sidebar.getByRole('button', { name: /Modules and Ports/i }).click();

    // Page navigated
    await expect(page.getByTestId('lesson-title')).toHaveText('Modules and Ports', { timeout: 10_000 });
  });

  test('desktop sidebar has nav buttons visible', async ({ page }) => {
    await page.setViewportSize(WIDE);
    await page.goto('/');
    // The inner sidebar container should be in the DOM and visible
    const sidebar = page.locator('[data-sidebar="sidebar"]');
    await expect(sidebar).toBeVisible();
    // Chapter buttons are accessible directly
    await expect(sidebar.getByRole('button', { name: 'Introduction' })).toBeVisible();
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
    await page.waitForTimeout(300);
    const restoredWidth = await gap.evaluate(el => el.getBoundingClientRect().width);
    expect(restoredWidth).toBeGreaterThan(0);
  });
});
