import { defineConfig } from '@playwright/test';

export default defineConfig({
  testDir: './e2e',
  timeout: 180_000,
  fullyParallel: false,
  forbidOnly: false,
  retries: 0,
  reporter: [['list']],
  use: {
    channel: 'chromium',
    headless: true,
    launchOptions: {
      args: [
        '--use-angle=swiftshader',
        '--enable-webgl',
        '--enable-unsafe-swiftshader',
        '--ignore-gpu-blocklist'
      ]
    },
    baseURL: 'https://thomasnormal.github.io/sv-tutorial',
    trace: 'on-first-retry',
    screenshot: 'only-on-failure'
  },
  // No webServer block — testing against the already-deployed site
});
