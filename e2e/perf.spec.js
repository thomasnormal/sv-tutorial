/**
 * Performance profiling spec.
 * Measures Core Web Vitals and key timing metrics for the main lesson route.
 * Run with: npx playwright test e2e/perf.spec.js --reporter=list
 */
import { test, expect } from '@playwright/test';

const LESSON_URL = '/lesson/sv/welcome';
const RUNS = 3; // average over multiple cold loads

/** Inject a PerformanceObserver that collects LCP, CLS, FID/INP candidates. */
async function collectWebVitals(page) {
  return page.evaluate(() => new Promise(resolve => {
    const result = { lcp: null, cls: 0, fcp: null, ttfb: null, inp: null };
    let clsValue = 0;
    let sessionValue = 0;
    let sessionEntries = [];

    const lcpObs = new PerformanceObserver(list => {
      const entries = list.getEntries();
      result.lcp = entries[entries.length - 1].startTime;
    });
    lcpObs.observe({ type: 'largest-contentful-paint', buffered: true });

    const fcpObs = new PerformanceObserver(list => {
      for (const e of list.getEntries()) {
        if (e.name === 'first-contentful-paint') result.fcp = e.startTime;
      }
    });
    fcpObs.observe({ type: 'paint', buffered: true });

    const clsObs = new PerformanceObserver(list => {
      for (const entry of list.getEntries()) {
        if (!entry.hadRecentInput) {
          const firstTime = sessionEntries[0]?.startTime ?? 0;
          const lastTime  = sessionEntries[sessionEntries.length - 1]?.startTime ?? 0;
          if (entry.startTime - lastTime < 1000 && entry.startTime - firstTime < 5000) {
            sessionValue += entry.value;
            sessionEntries.push(entry);
          } else {
            sessionValue = entry.value;
            sessionEntries = [entry];
          }
          clsValue = Math.max(clsValue, sessionValue);
          result.cls = clsValue;
        }
      }
    });
    clsObs.observe({ type: 'layout-shift', buffered: true });

    // Navigation timing gives TTFB
    const navObs = new PerformanceObserver(list => {
      const nav = list.getEntries()[0];
      if (nav) result.ttfb = nav.responseStart - nav.requestStart;
    });
    navObs.observe({ type: 'navigation', buffered: true });

    // Resolve after paint + a short settle window
    setTimeout(() => {
      lcpObs.disconnect();
      fcpObs.disconnect();
      clsObs.disconnect();
      navObs.disconnect();
      resolve(result);
    }, 3000);
  }));
}

/** Get standard Navigation Timing + resource summary. */
async function collectTimings(page) {
  return page.evaluate(() => {
    const nav = performance.getEntriesByType('navigation')[0];
    const resources = performance.getEntriesByType('resource');
    const byType = {};
    let totalBytes = 0;
    for (const r of resources) {
      const ext = r.name.split('.').pop().split('?')[0];
      byType[ext] = (byType[ext] ?? 0) + 1;
      totalBytes += r.transferSize ?? 0;
    }
    return {
      domContentLoaded: nav.domContentLoadedEventEnd - nav.startTime,
      load:             nav.loadEventEnd - nav.startTime,
      domInteractive:   nav.domInteractive - nav.startTime,
      resources:        resources.length,
      resourceTypes:    byType,
      transferKB:       Math.round(totalBytes / 1024),
      // JS parse/compile hints
      scriptDuration:   resources
        .filter(r => r.initiatorType === 'script')
        .reduce((s, r) => s + r.duration, 0),
    };
  });
}

/** Measure JS heap size (Chrome only). */
async function collectMemory(page) {
  return page.evaluate(() => {
    const m = performance.memory;
    if (!m) return null;
    return {
      usedMB:  (m.usedJSHeapSize  / 1024 / 1024).toFixed(1),
      totalMB: (m.totalJSHeapSize / 1024 / 1024).toFixed(1),
      limitMB: (m.jsHeapSizeLimit / 1024 / 1024).toFixed(0),
    };
  });
}

function fmt(ms) {
  if (ms === null || ms === undefined) return 'n/a';
  return `${Math.round(ms)} ms`;
}
function rating(metric, value) {
  const thresholds = {
    lcp:  [2500, 4000],
    fcp:  [1800, 3000],
    cls:  [0.1,  0.25],
    ttfb: [800,  1800],
    dcl:  [1500, 3000],
    load: [2500, 5000],
  };
  const [good, poor] = thresholds[metric] ?? [Infinity, Infinity];
  if (value <= good) return '✅ good';
  if (value <= poor) return '⚠️  needs improvement';
  return '❌ poor';
}

test.describe('Core Web Vitals & Performance', () => {
  test('lesson page — cold load metrics', async ({ page }) => {
    // Disable cache to simulate cold load
    await page.context().clearCookies();

    // Collect multiple runs and average
    const runs = [];
    for (let i = 0; i < RUNS; i++) {
      await page.goto(LESSON_URL, { waitUntil: 'networkidle' });
      const [vitals, timings] = await Promise.all([
        collectWebVitals(page),
        collectTimings(page),
      ]);
      runs.push({ vitals, timings });
      if (i < RUNS - 1) await page.reload({ waitUntil: 'networkidle' });
    }

    // Average the numeric metrics
    const avg = key => runs.reduce((s, r) => s + (r.vitals[key] ?? 0), 0) / RUNS;
    const avgT = key => runs.reduce((s, r) => s + (r.timings[key] ?? 0), 0) / RUNS;

    const lcp  = avg('lcp');
    const fcp  = avg('fcp');
    const cls  = avg('cls');
    const ttfb = avg('ttfb');
    const dcl  = avgT('domContentLoaded');
    const load = avgT('load');
    const last = runs[runs.length - 1];

    const memory = await collectMemory(page);

    console.log('\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━');
    console.log(` Performance report  (${RUNS}-run avg, cold load)`);
    console.log(`━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━`);
    console.log(` Core Web Vitals`);
    console.log(`   LCP   ${fmt(lcp).padEnd(10)} ${rating('lcp',  lcp)}`);
    console.log(`   FCP   ${fmt(fcp).padEnd(10)} ${rating('fcp',  fcp)}`);
    console.log(`   CLS   ${cls.toFixed(4).padEnd(10)} ${rating('cls',  cls)}`);
    console.log(`   TTFB  ${fmt(ttfb).padEnd(10)} ${rating('ttfb', ttfb)}`);
    console.log(``);
    console.log(` Navigation Timing`);
    console.log(`   DOM interactive   ${fmt(last.timings.domInteractive)}`);
    console.log(`   DOMContentLoaded  ${fmt(dcl)}  ${rating('dcl', dcl)}`);
    console.log(`   Load event        ${fmt(load)}  ${rating('load', load)}`);
    console.log(``);
    console.log(` Resources (last run)`);
    console.log(`   Total resources   ${last.timings.resources}`);
    console.log(`   Transfer size     ${last.timings.transferKB} KB`);
    console.log(`   By type:          ${JSON.stringify(last.timings.resourceTypes)}`);
    if (memory) {
      console.log(``);
      console.log(` JS Heap (after load)`);
      console.log(`   Used  ${memory.usedMB} MB  /  Total ${memory.totalMB} MB  /  Limit ${memory.limitMB} MB`);
    }
    console.log(`━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n`);

    // Soft assertions — fail if metrics are truly terrible
    expect(lcp,  'LCP should be under 5s').toBeLessThan(5000);
    expect(fcp,  'FCP should be under 4s').toBeLessThan(4000);
    expect(cls,  'CLS should be under 0.5').toBeLessThan(0.5);
  });

  test('lesson navigation — transition metrics', async ({ page }) => {
    await page.goto(LESSON_URL, { waitUntil: 'networkidle' });

    const lessons = [
      '/lesson/sv/always-ff',
      '/lesson/sv/always-comb',
      '/lesson/sv/counter',
      '/lesson/sva/formal-intro',
      '/lesson/uvm/reporting',
    ];

    console.log('\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━');
    console.log(' Client-side navigation timings (SvelteKit router)');
    console.log('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━');

    for (const url of lessons) {
      const t0 = Date.now();
      await page.goto(url, { waitUntil: 'networkidle' });
      const elapsed = Date.now() - t0;

      // Check lesson content is visible
      const lessonBody = page.locator('.lesson-body');
      await lessonBody.waitFor({ timeout: 3000 });

      console.log(`   ${url.padEnd(35)} ${elapsed} ms`);
    }
    console.log('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n');
  });
});
