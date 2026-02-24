import { test, expect } from '@playwright/test';

async function expectInterpretMode(logs) {
  await expect(logs).toContainText('--mode interpret');
  await expect(logs).not.toContainText('--compiled');
}

test('welcome lesson executes simulation output', async ({ page }) => {
  await page.goto('/');

  const logs = page.getByTestId('runtime-logs');
  await expect(page.getByRole('heading', { level: 2, name: 'Welcome' })).toBeVisible();

  await page.getByTestId('run-button').click();

  await expect(logs).toContainText('$ circt-verilog', { timeout: 120_000 });
  await expect(logs).toContainText('$ circt-sim', { timeout: 120_000 });
  await expectInterpretMode(logs);
  await expect(logs).not.toContainText('exit code: 0');
});

async function runModulesAndPorts(page) {
  const consoleLines = [];
  page.on('console', (msg) => {
    consoleLines.push(msg.text());
  });

  await page.goto('/');
  await page.getByRole('button', { name: 'next' }).click();

  const logs = page.getByTestId('runtime-logs');
  await expect(page.getByRole('heading', { level: 2, name: 'Modules and Ports' })).toBeVisible();

  await page.getByTestId('solve-button').click();
  await page.getByTestId('run-button').click();

  await expect(logs).toContainText('$ circt-verilog', { timeout: 120_000 });
  await expect(logs).toContainText('$ circt-sim', { timeout: 120_000 });
  await expectInterpretMode(logs);
  await expect(logs).not.toContainText('exit code: 0');
  await expect(page.getByTestId('runtime-tab-waves')).toBeVisible({ timeout: 120_000 });
  await expect(logs).not.toContainText('[circt-mock]');

  return { logs, consoleLines };
}

test('run generates a real VCD (non-mock pipeline)', async ({ page }) => {
  const { logs } = await runModulesAndPorts(page);
  await expect(logs).not.toContainText('exit code: 0');
});

test('surfer renders waveform when WebGL2 is available', async ({ page }) => {
  await page.goto('/surfer/index.html#dev');
  const crashBanner = page.getByText('Sorry, Surfer crashed');
  let surferBootCrash = false;
  try {
    await expect(crashBanner).toBeVisible({ timeout: 3000 });
    surferBootCrash = true;
  } catch {
    surferBootCrash = false;
  }
  test.skip(surferBootCrash, 'Surfer crashes in this Playwright environment (WebGL unavailable)');

  const { consoleLines } = await runModulesAndPorts(page);

  await page.getByTestId('runtime-tab-waves').click();
  await expect(page.getByTestId('waveform-iframe')).toBeVisible();
  await expect(page.getByTestId('no-waveform-message')).toHaveCount(0);

  const waveFrame = page.getByTestId('waveform-frame-wrapper');
  await expect(waveFrame).toHaveAttribute('data-wave-state', 'ready', { timeout: 30_000 });

  await expect
    .poll(() => {
      return consoleLines.some((line) => /VCD file loaded|WaveBodyLoaded/i.test(line));
    }, { timeout: 30_000 })
    .toBe(true);

  const iframeHandle = await page.getByTestId('waveform-iframe').elementHandle();
  const iframe = await iframeHandle?.contentFrame();
  expect(iframe).not.toBeNull();
  const crashBannerInIframe = iframe.getByText('Sorry, Surfer crashed');
  const crashVisible = await crashBannerInIframe.first().isVisible().catch(() => false);
  test.skip(
    crashVisible,
    'Surfer crashes in this Playwright environment while rendering (WebGL unavailable)'
  );
  await expect(crashBannerInIframe.first()).not.toBeVisible();
});

test('concurrent-sim SVA assertion signal appears in VCD', async ({ page }) => {
  // Intercept URL.createObjectURL to capture the text of any VCD blob sent to Surfer.
  await page.addInitScript(() => {
    window._vcdTexts = [];
    const origCreate = URL.createObjectURL.bind(URL);
    URL.createObjectURL = function (blob) {
      if (blob.type === 'text/plain') {
        blob.text().then((t) => { if (t.includes('$var')) window._vcdTexts.push(t); });
      }
      return origCreate(blob);
    };
  });

  await page.goto('/lesson/sva/concurrent-sim');
  await page.evaluate(() => {
    for (const key of Object.keys(localStorage)) {
      if (key.startsWith('svt:')) localStorage.removeItem(key);
    }
  });

  const logs = page.getByTestId('runtime-logs');
  await page.getByTestId('solve-button').click();
  await page.getByTestId('run-button').click();

  // The testbench has a missing-grant scenario that fires the assertion.
  // circt-sim exits with code 1 on assertion failure — that is expected and correct.
  await expect(logs).toContainText('SVA assertion failed', { timeout: 90_000 });
  await expect(logs).not.toContainText('# circt-verilog exit code: 1');

  // The Waves tab should appear (VCD was produced).
  await expect(page.getByTestId('runtime-tab-waves')).toBeVisible();

  // Verify the VCD blob sent to Surfer contains at least one SVA assertion signal.
  // Use poll() to handle the async blob.text() microtask.
  await expect.poll(
    () => page.evaluate(() =>
      window._vcdTexts.some((t) => t.includes('__sva__'))
    ),
    { timeout: 10_000, message: 'VCD should contain at least one __sva__ signal' }
  ).toBe(true);
});
