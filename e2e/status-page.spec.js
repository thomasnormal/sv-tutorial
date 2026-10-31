import { test, expect } from '@playwright/test';

test('generated status page covers every lesson', async ({ page }) => {
  await page.goto('/status');
  await expect(page.getByTestId('status-page')).toBeVisible();
  await expect(page.getByTestId('status-row')).toHaveCount(83);
  await expect(page.getByTestId('status-summary')).toContainText('PASS: 26');
  await expect(page.getByTestId('status-summary')).toContainText('Mox refusal: 41');
  await expect(page.getByTestId('status-summary')).toContainText('Environment: 16');
  await expect(page.getByTestId('matrix-diff')).toContainText('What changed');
  await expect(page.getByTestId('matrix-diff')).toContainText('sva/immediate-assert');
});

test('affected lesson exposes its measured limitation and native variant', async ({ page }) => {
  await page.goto('/lesson/sva/clock-delay');
  await expect(page.getByTestId('lesson-status-badge')).toHaveText('Mox refusal');
  const limitation = page.getByTestId('known-limitation');
  await expect(limitation).toContainText('IEEE 1800-2023 §16.10.1');
  await expect(limitation).toContainText('temporal-property-evaluator-not-admitted');
  await expect(limitation).toContainText('mox-verilog --ir-llhd');
});
