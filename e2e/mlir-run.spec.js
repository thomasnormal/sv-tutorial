import { test, expect } from '@playwright/test';

test('MLIR intro: run executes via circt-sim without SV-source error', async ({ page }) => {
  await page.goto('/lesson/mlir/intro');
  await expect(page.getByTestId('lesson-title')).toHaveText('What is MLIR?');

  await page.getByTestId('run-button').click();

  const logs = page.getByTestId('runtime-logs');
  await expect(logs).toContainText('$ circt-sim', { timeout: 120_000 });
  await expect(logs).toContainText('# using MLIR source: /src/adder.mlir', { timeout: 120_000 });
  await expect(logs).not.toContainText('# no SystemVerilog source files found in workspace');
  await expect(logs).not.toContainText('# no SystemVerilog or MLIR source files found in workspace');
  await expect(logs).not.toContainText('exit code: 1');
});
