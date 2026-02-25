<script>
  import { onDestroy, onMount } from 'svelte';

  let { vcd = null, hasRun = false, darkMode = false, signalsReady = $bindable(false) } = $props();

  let iframeEl = $state(null);
  let iframeLoaded = $state(false);
  let surferReady = $state(false);
  let waveReadySource = $state('none');
  // null = checking, true = available, false = not installed
  let surferAvailable = $state(null);

  let _blobUrl = null;
  let _cmdBlobUrl = null;
  let _retryTimers = [];
  let _readyFallbackTimer = null;
  // Two quick retries absorb transient startup races on slower hosts.
  const LOAD_RETRY_MS = [0, 500];
  // Extra chrome-hiding passes after iframe load — WASM may still be initialising.
  const CHROME_HIDE_RETRY_MS = [0, 600, 1800];
  // Extra wait after last load retry before sending the scope command file.
  const CMD_EXTRA_DELAY_MS = 500;
  // Fallback delay to mark signals ready if Surfer never emits waves-loaded.
  const READY_FALLBACK_MS = 2000;

  function clearLoadRetries() {
    for (const t of _retryTimers) clearTimeout(t);
    _retryTimers = [];
  }

  function clearReadyFallback() {
    if (_readyFallbackTimer) {
      clearTimeout(_readyFallbackTimer);
      _readyFallbackTimer = null;
    }
  }

  function clearWaveBlobs() {
    if (_blobUrl) {
      URL.revokeObjectURL(_blobUrl);
      _blobUrl = null;
    }
    if (_cmdBlobUrl) {
      URL.revokeObjectURL(_cmdBlobUrl);
      _cmdBlobUrl = null;
    }
  }

  import { base } from '$app/paths';
  // Ensure surfer paths are always absolute regardless of base ('' vs '/foo').
  const BASE = base ? `${base}/` : '/';

  // Probe surfer.js with GET and MIME check. Vite preview can return SPA fallback
  // HTML with a false-positive 200 for missing assets.
  $effect(() => {
    fetch(`${BASE}surfer/surfer.js`, { method: 'GET', cache: 'force-cache' })
      .then((r) => {
        const contentType = (r.headers.get('content-type') || '').toLowerCase();
        const isScriptMime = /javascript|ecmascript/.test(contentType);
        surferAvailable = r.ok && isScriptMime;
      })
      .catch(() => { surferAvailable = false; });
  });

  // Re-send whenever VCD data or iframe readiness changes.
  $effect(() => {
    const text = vcd;
    const el = iframeEl;
    const loaded = iframeLoaded;
    if (!text || !el || !loaded) return;
    sendVcd(el, text);
  });

  // When no VCD is available, clear pending loads and release blob URLs so
  // stale waveform data cannot leak into the next lesson/run.
  $effect(() => {
    if (vcd) return;
    clearLoadRetries();
    clearReadyFallback();
    clearWaveBlobs();
    signalsReady = false;
    waveReadySource = 'none';
  });

  // App warm palette — must stay in sync with src/app.css custom color tokens.
  // Colors are 6-char hex strings (no '#') as required by Surfer's TOML parser.
  const SURFER_THEME = [
    'foreground = "1e2a2c"',
    'border_color = "d5cbb2"',
    'canvas_colors = { background = "fff4ef", alt_background = "f5f1e6", foreground = "1e2a2c" }',
    'primary_ui_color = { background = "fffdf7", foreground = "1e2a2c" }',
    'secondary_ui_color = { background = "efe8d7", foreground = "1e2a2c" }',
    'selected_elements_colors = { background = "d5cbb2", foreground = "1e2a2c" }',
    'highlight_background = "e7f6f4"',
    'clock_highlight_cycle = "f0ebe0"',
    'clock_highlight_line = { color = "d5cbb2", width = 1 }',
    'variable_default = "0d6f72"',
    'cursor = { color = "0d6f72", width = 2 }',
    'gesture = { color = "0d6f72", width = 2 }',
  ].join('\n');

  function surferMsg(cw, msg) {
    cw.postMessage({ command: 'InjectMessage', message: JSON.stringify(msg) }, '*');
  }

  // Exported so parent can call via bind:this={waveformRef}; waveformRef.sendCmd('zoom_in')
  export function sendCmd(cmd) {
    const cw = iframeEl?.contentWindow;
    if (!cw) return;
    const url = URL.createObjectURL(new Blob([cmd + '\n'], { type: 'text/plain' }));
    surferMsg(cw, { LoadCommandFileFromUrl: url });
    setTimeout(() => URL.revokeObjectURL(url), 5000);
  }

  function applyChrome(cw, dark = false) {
    // All messages are idempotent — safe to call on every retry.
    surferMsg(cw, { SetMenuVisible: false });
    surferMsg(cw, { SetToolbarVisible: false });
    surferMsg(cw, { SetStatusbarVisible: false });
    surferMsg(cw, { SetSidePanelVisible: false });
    // Increase UI zoom so signal rows are readable at typical pane heights.
    surferMsg(cw, { SetUIZoomFactor: 1.5 });
    if (dark) {
      surferMsg(cw, { SelectTheme: 'dark+' });
    } else {
      surferMsg(cw, { SelectTheme: 'light+' });
      surferMsg(cw, { SetConfigFromString: SURFER_THEME });
    }
  }

  // Parse VCD and return { id, name } for the first variable that has actual
  // value transitions after the initial $dumpvars block.  Returns null if none.
  function firstTransitioningVar(vcdText) {
    // Collect {id (identifier code), name} in declaration order.
    // VCD: $var type width identifier name $end
    const vars = [];
    for (const m of vcdText.matchAll(/\$var\s+\w+\s+\d+\s+(\S+)\s+(\S+)[^$]*\$end/g)) {
      vars.push({ id: m[1], name: m[2] });
    }
    if (vars.length === 0) return null;

    // Find $enddefinitions and skip past the $dumpvars initial-state block so
    // we only look at changes that occur at real simulation timestamps.
    const enddefs = vcdText.search(/\$enddefinitions\b/);
    if (enddefs === -1) return null;
    let rest = vcdText.slice(enddefs);
    const dumpStart = rest.indexOf('$dumpvars');
    if (dumpStart !== -1) {
      const dumpEnd = rest.indexOf('$end', dumpStart);
      if (dumpEnd !== -1) rest = rest.slice(dumpEnd + 4);
    }
    // Find the first timestamp after the dumpvars block.
    const firstTs = rest.search(/#\d/);
    if (firstTs === -1) return null;
    rest = rest.slice(firstTs);

    // Collect all identifiers that change at any point after dumpvars.
    const transitioning = new Set();
    for (const m of rest.matchAll(/^[01xzXZ]([!-~]+)|^b[01xzXZ]+\s+([!-~]+)/gm)) {
      transitioning.add(m[1] ?? m[2]);
    }

    for (const v of vars) {
      if (transitioning.has(v.id)) return v;
    }
    return null;
  }

  function sendVcd(el, text) {
    clearLoadRetries();
    clearReadyFallback();
    clearWaveBlobs();
    signalsReady = false;
    waveReadySource = 'none';

    const blob = new Blob([text], { type: 'text/plain' });
    const url = URL.createObjectURL(blob);
    _blobUrl = url;

    // Progressive retries absorb Surfer's WASM init time on slower hosts.
    // Chrome-hiding messages are sent alongside LoadUrl on each attempt.
    const dark = darkMode;
    for (const ms of LOAD_RETRY_MS) {
      const t = setTimeout(() => {
        const cw = el?.contentWindow;
        if (!cw) return;
        applyChrome(cw, dark);
        cw.postMessage({ command: 'LoadUrl', url }, '*');
      }, ms);
      _retryTimers.push(t);
    }

    // After VCD is fully loaded, auto-populate with all signals from the root
    // scope and zoom to fit. Parse the VCD to find the first top-level scope
    // name, then build the command file dynamically via a blob URL.
    const rootScope = text.match(/\$scope\s+\w+\s+(\w+)\s*\$end/)?.[1];
    if (rootScope) {
      const cmd = `scope_add_recursive ${rootScope}\nzoom_fit\n`;
      _cmdBlobUrl = URL.createObjectURL(new Blob([cmd], { type: 'text/plain' }));
      const cmdUrl = _cmdBlobUrl;
      const cmdDelay = LOAD_RETRY_MS[LOAD_RETRY_MS.length - 1] + CMD_EXTRA_DELAY_MS;
      const t = setTimeout(() => {
        const cw = el?.contentWindow;
        if (!cw) return;
        surferMsg(cw, { LoadCommandFileFromUrl: cmdUrl });
      // Fire after the last load retry + parse time (VCDs are tiny, <20ms to parse).
      }, cmdDelay);
      _retryTimers.push(t);
      // Auto-select the first signal that has actual transitions so that
      // transition_next/prev work without requiring the user to click a row.
      //
      // Strategy (two-pronged):
      //   1. FocusItem(idx) — sets keyboard focus in the signal list.
      //   2. SetItemSelected — directly selects the item by its DisplayedItemRef id
      //      (obtained from Surfer's own id_of_name() WASM export), which is what
      //      transition_next actually navigates on.
      const firstVar = firstTransitioningVar(text);
      const focusTimer = setTimeout(async () => {
        const cw = el?.contentWindow;
        if (!cw) return;

        // 1. Focus by visible index as a baseline.
        const fallbackIdx = firstVar ? null : 0;
        let focusDone = false;

        // 2. Try the reliable path: use Surfer's id_of_name() to get the exact
        //    DisplayedItemRef, then both focus and select that item.
        if (firstVar && typeof cw.id_of_name === 'function') {
          try {
            const itemId = await cw.id_of_name(firstVar.name);
            if (itemId !== undefined) {
              // SetItemSelected selects the item (blue highlight) — this is the
              // state that transition_next/prev operates on.
              surferMsg(cw, { SetItemSelected: { item: itemId, selected: true } });
              // Also try to get the visible index for FocusItem.
              if (typeof cw.index_of_name === 'function') {
                const visIdx = await cw.index_of_name(firstVar.name);
                if (visIdx !== undefined) {
                  surferMsg(cw, { FocusItem: visIdx });
                  focusDone = true;
                }
              } else {
                focusDone = true; // SetItemSelected alone may be enough
              }
            }
          } catch { /* ignore — fall through to index-based fallback */ }
        }

        // Fallback: focus by declaration-order index.
        if (!focusDone) {
          surferMsg(cw, { FocusItem: fallbackIdx ?? 0 });
        }
      }, cmdDelay + 400);
      _retryTimers.push(focusTimer);
      // Keep the UI responsive if an older Surfer build does not emit
      // waves-loaded integration events.
      _readyFallbackTimer = setTimeout(() => {
        signalsReady = true;
        waveReadySource = 'fallback';
        _readyFallbackTimer = null;
      }, cmdDelay + READY_FALLBACK_MS);
    } else {
      _readyFallbackTimer = setTimeout(() => {
        signalsReady = true;
        waveReadySource = 'fallback';
        _readyFallbackTimer = null;
      }, READY_FALLBACK_MS);
    }
  }

  function onIframeLoad() {
    iframeLoaded = true;
    surferReady = false;
    // Hide chrome as soon as possible after load, even before VCD arrives.
    // Retried because WASM may not be ready yet.
    for (const ms of CHROME_HIDE_RETRY_MS) {
      setTimeout(() => {
        const cw = iframeEl?.contentWindow;
        if (cw) applyChrome(cw, darkMode);
      }, ms);
    }
  }

  // Re-apply theme when dark mode is toggled while the iframe is alive.
  $effect(() => {
    const dark = darkMode;
    const cw = iframeEl?.contentWindow;
    if (!cw || !surferReady) return;
    applyChrome(cw, dark);
  });

  function onParentMessage(event) {
    const frameWindow = iframeEl?.contentWindow;
    if (!frameWindow || event.source !== frameWindow) return;
    const data = event.data || {};
    if (data?.source !== 'surfer') return;
    if (data.type === 'listener-ready' || data.type === 'engine-ready') {
      surferReady = true;
    }
    if (data.type === 'waves-loaded') {
      clearReadyFallback();
      signalsReady = true;
      waveReadySource = 'surfer';
    }
  }

  onMount(() => {
    window.addEventListener('message', onParentMessage);
    return () => {
      window.removeEventListener('message', onParentMessage);
    };
  });

  onDestroy(() => {
    clearLoadRetries();
    clearReadyFallback();
    clearWaveBlobs();
  });
</script>

{#if surferAvailable === false}
  <div class="h-full flex flex-col items-center justify-center gap-3 text-muted-foreground text-sm text-center p-4">
    <p class="m-0">Surfer waveform viewer is not installed.</p>
    <p class="m-0">Run the setup script to download the web build:</p>
    <pre class="m-0 bg-logs-bg text-logs-text rounded-[8px] px-4 py-2 font-mono text-[0.8rem]">scripts/setup-surfer.sh</pre>
  </div>

{:else if surferAvailable}
  {#if vcd}
    <div
      data-testid="waveform-frame-wrapper"
      data-wave-state={signalsReady ? 'ready' : 'loading'}
      data-wave-ready-source={waveReadySource}
      class="relative w-full h-full"
    >
      <iframe
        bind:this={iframeEl}
        src="{BASE}surfer/index.html?svtutorial=20260223#dev"
        title="Surfer Waveform Viewer"
        onload={onIframeLoad}
        data-testid="waveform-iframe"
        class="w-full h-full border-none"
      ></iframe>
      {#if !signalsReady}
        <div data-testid="waveform-loading-overlay" class="absolute inset-0 flex items-center justify-center
                    bg-surface text-muted-foreground text-sm
                    pointer-events-none">
          Loading waveform…
        </div>
      {/if}
    </div>
  {:else}
    <div data-testid="no-waveform-message" class="h-full flex items-center justify-center text-muted-foreground text-sm text-center p-4">
      <span>{hasRun ? 'no waveform vcd found' : 'Run the simulation to generate waveform data.'}</span>
    </div>
  {/if}

{:else}
  <div class="h-full flex items-center justify-center text-muted-foreground text-sm">
    <span>Checking for Surfer…</span>
  </div>
{/if}

