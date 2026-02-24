<script>
  import { lessons, parts } from './tutorial-data.js';
  import { createCirctWasmAdapter } from './runtime/circt-adapter.js';
  import { afterUpdate, onMount } from 'svelte';
  import { Button } from '$lib/components/ui/button';
  import { Tabs, TabsList, TabsTrigger } from '$lib/components/ui/tabs';
  import CodeEditor from '$lib/components/CodeEditor.svelte';
  import WaveformViewer from '$lib/components/WaveformViewer.svelte';

  const circt = createCirctWasmAdapter();

  let hSplit = 33;  // lesson pane % of main section width
  let vSplit = 65;  // editor pane % of lab section height

  let lessonIndex = 0;
  let lesson = lessons[0];
  let starterFiles = cloneFiles(lesson.files.a);
  let solutionFiles = mergeFiles(starterFiles, lesson.files.b);

  let selectedFile = lesson.focus;
  let workspace = cloneFiles(starterFiles);
  let logs = lessonBootLogs(lesson.title);
  let activeRuntimeTab = 'logs'; // 'logs' | 'waves'
  let running = false;
  let runMode = 'sim';   // 'sim' | 'bmc' | 'lec' — which button triggered the current run
  let runPhase = 'idle'; // 'idle' | 'compiling' | 'running'
  let checkingRuntime = false;
  let runtimeOk = null;
  let lastWaveform = null;
  let hasRunOnce = false;
  let sidebarOpen = true;
  let expandedChapters = new Set([lessons[0].chapterTitle]);
  let sidebarInnerEl;
  let copyEnabled = false;
  let showCopyModal = false;
  let copyEnableChecked = false;

  afterUpdate(() => {
    sidebarInnerEl?.querySelector('[data-active="true"]')?.scrollIntoView({ block: 'nearest' });
  });

  onMount(() => {
    if (sessionStorage.getItem('copyEnabled') === 'true') copyEnabled = true;

    const params = new URLSearchParams(window.location.search);
    const n = Number(params.get('lesson'));
    if (Number.isFinite(n) && n >= 1 && n <= lessons.length) {
      lessonIndex = n - 1;
      ensureChapterVisible(n - 1);
    }
  });

  function handleCopy(e) {
    if (!copyEnabled && e.target?.closest('.lesson-body')) {
      e.preventDefault();
      copyEnableChecked = false;
      showCopyModal = true;
    }
  }

  function onCopyModalOk() {
    if (copyEnableChecked) {
      copyEnabled = true;
      sessionStorage.setItem('copyEnabled', 'true');
    }
    showCopyModal = false;
  }

  $: {
    const url = new URL(window.location.href);
    if (lessonIndex === 0) {
      url.searchParams.delete('lesson');
    } else {
      url.searchParams.set('lesson', String(lessonIndex + 1));
    }
    history.replaceState(null, '', url.toString());
  }

  function onKeydown(e) {
    if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
      e.preventDefault();
      runSim();
    }
  }

  $: lesson = lessons[lessonIndex];
  $: starterFiles = cloneFiles(lesson.files.a);
  $: solutionFiles = mergeFiles(starterFiles, lesson.files.b);
  $: hasSolution = Object.keys(lesson.files.b).length > 0;
  $: completed = hasSolution && filesEqual(workspace, solutionFiles);
  $: breadcrumbs = `${lesson.partTitle} / ${lesson.chapterTitle} / ${lesson.title}`;
  $: hasWaveform = typeof lastWaveform?.text === 'string' && lastWaveform.text.length > 0;
  $: if (!hasWaveform && activeRuntimeTab === 'waves') activeRuntimeTab = 'logs';

  $: {
    lesson;
    selectedFile = lesson.focus;
    workspace = cloneFiles(starterFiles);
    logs = lessonBootLogs(lesson.title);
    activeRuntimeTab = 'logs';
    runtimeOk = null;
    lastWaveform = null;
    hasRunOnce = false;
  }

  function cloneFiles(files) {
    return JSON.parse(JSON.stringify(files));
  }

  function lessonBootLogs(_title) {
    return [];
  }

  function mergeFiles(a, b) {
    return { ...cloneFiles(a), ...cloneFiles(b) };
  }

  function topNameFromFocus(path) {
    const filename = path.split('/').pop() || 'top.sv';
    return filename.replace(/\.[^.]+$/, '');
  }

  function normalize(text) {
    return String(text).replace(/\s+/g, ' ').trim();
  }

  function filesEqual(a, b) {
    const aKeys = Object.keys(a).sort();
    const bKeys = Object.keys(b).sort();

    if (aKeys.length !== bKeys.length) return false;

    for (let i = 0; i < aKeys.length; i += 1) {
      const aKey = aKeys[i];
      const bKey = bKeys[i];
      if (aKey !== bKey) return false;
      if (normalize(a[aKey]) !== normalize(b[bKey])) return false;
    }

    return true;
  }

  function toggleChapter(title) {
    if (expandedChapters.has(title)) {
      expandedChapters = new Set([...expandedChapters].filter(t => t !== title));
    } else {
      expandedChapters = new Set([...expandedChapters, title]);
    }
  }

  function ensureChapterVisible(idx) {
    const chapterTitle = lessons[idx]?.chapterTitle;
    if (chapterTitle && !expandedChapters.has(chapterTitle)) {
      expandedChapters = new Set([...expandedChapters, chapterTitle]);
    }
  }

  function step(delta) {
    const nextIndex = lessonIndex + delta;
    if (nextIndex < 0 || nextIndex >= lessons.length) return;
    lessonIndex = nextIndex;
    ensureChapterVisible(nextIndex);
  }

  function toggleSolve() {
    if (!hasSolution) return;

    if (completed) {
      workspace = cloneFiles(starterFiles);
      logs = [...logs, 'Reset to starter files'];
      return;
    }

    workspace = cloneFiles(solutionFiles);
    logs = [...logs, 'Applied solution files'];
  }

  function onEdit(newValue) {
    workspace = { ...workspace, [selectedFile]: newValue };
  }

  function isStdoutEntry(entry) {
    return typeof entry === 'string' && entry.startsWith('[stdout] ');
  }

  function isStderrEntry(entry) {
    return typeof entry === 'string' && entry.startsWith('[stderr] ');
  }

  function stripStreamPrefix(entry) {
    if (isStdoutEntry(entry)) return entry.slice('[stdout] '.length);
    if (isStderrEntry(entry)) return entry.slice('[stderr] '.length);
    return entry;
  }

  function startHResize(e) {
    e.preventDefault();
    const section = e.currentTarget.parentElement;
    const totalW = section.getBoundingClientRect().width;
    const startX = e.clientX, startSplit = hSplit;
    const onMove = ev => {
      const raw = startSplit + (ev.clientX - startX) / totalW * 100;
      hSplit = Math.min(Math.max(raw, 200 / totalW * 100), (totalW - 300) / totalW * 100);
    };
    const onUp = () => {
      window.removeEventListener('pointermove', onMove);
      window.removeEventListener('pointerup', onUp);
    };
    window.addEventListener('pointermove', onMove);
    window.addEventListener('pointerup', onUp);
  }

  function startVResize(e) {
    e.preventDefault();
    const lab = e.currentTarget.parentElement;
    const totalH = lab.getBoundingClientRect().height;
    const startY = e.clientY, startSplit = vSplit;
    const onMove = ev => {
      const raw = startSplit + (ev.clientY - startY) / totalH * 100;
      vSplit = Math.min(Math.max(raw, 150 / totalH * 100), (totalH - 150) / totalH * 100);
    };
    const onUp = () => {
      window.removeEventListener('pointermove', onMove);
      window.removeEventListener('pointerup', onUp);
    };
    window.addEventListener('pointermove', onMove);
    window.addEventListener('pointerup', onUp);
  }

  async function runSim(mode = 'sim') {
    if (running) return;
    running = true;
    runMode = mode;
    runPhase = 'compiling';
    lastWaveform = null;
    logs = []; // clear terminal on each new run

    const useBmc = mode === 'bmc';
    const useLec = mode === 'lec';

    try {
      const onStatus = (status) => {
        if (status === 'compiling') {
          runPhase = 'compiling';
          return;
        }
        if (status === 'running') {
          runPhase = 'running';
        }
      };

      if (lesson.runner === 'cocotb') {
        const result = await circt.runCocotb({
          files: workspace,
          top: topNameFromFocus(lesson.focus),
          onStatus
        });
        logs = [...logs, ...result.logs];
      } else if (mode === 'lec') {
        const result = await circt.runLec({
          files: workspace,
          module1: lesson.module1 || 'Spec',
          module2: lesson.module2 || 'Impl',
          onStatus
        });
        logs = [...logs, ...result.logs];
      } else if (useBmc) {
        const result = await circt.runBmc({
          files: workspace,
          top: topNameFromFocus(lesson.focus),
          onStatus
        });
        logs = [...logs, ...result.logs];
      } else {
        const result = await circt.run({
          files: workspace,
          top: topNameFromFocus(lesson.focus),
          simulate: lesson.simulate,
          onStatus
        });
        logs = [...logs, ...result.logs];
        lastWaveform = result.waveform;
      }
    } finally {
      hasRunOnce = true;
      running = false;
      runMode = 'sim';
      runPhase = 'idle';
    }
  }

  async function selfCheckRuntime() {
    if (checkingRuntime) return;
    checkingRuntime = true;

    try {
      const result = await circt.selfCheck({ lesson });
      runtimeOk = result.ok;
      logs = [...logs, ...result.logs];
    } finally {
      checkingRuntime = false;
    }
  }
</script>

<svelte:window on:keydown={onKeydown} on:copy={handleCopy} />
<main class="h-dvh p-3 flex flex-col gap-[0.7rem] font-sans overflow-hidden">
  <header class="bg-surface border border-border rounded-[14px] px-4 py-[0.9rem] shadow-app flex justify-between gap-4 items-center flex-wrap">
    <div class="flex items-center gap-3">
      <button
        on:click={() => (sidebarOpen = !sidebarOpen)}
        class="flex items-center justify-center w-8 h-8 rounded-[8px] border border-border hover:bg-surface-2 transition-colors text-muted-foreground flex-shrink-0"
        aria-label={sidebarOpen ? 'Close sidebar' : 'Open sidebar'}
      >
        {#if sidebarOpen}
          <svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
            <rect x="3" y="3" width="18" height="18" rx="2"/>
            <path d="M9 3v18"/>
            <path d="m15 9-3 3 3 3"/>
          </svg>
        {:else}
          <svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
            <rect x="3" y="3" width="18" height="18" rx="2"/>
            <path d="M9 3v18"/>
            <path d="m13 15 3-3-3-3"/>
          </svg>
        {/if}
      </button>
      <div class="flex flex-col items-start gap-[0.2rem]">
        <h1 class="m-0 text-xl tracking-[0.01em]">SV Tutorial Lab</h1>
        <p class="m-0 text-muted-foreground text-sm">{breadcrumbs}</p>
      </div>
    </div>

    <div class="flex items-center gap-[0.7rem] flex-wrap">
      <Button variant="outline" size="sm" onclick={() => step(-1)} disabled={lessonIndex === 0}>prev</Button>
      <Button variant="outline" size="sm" onclick={() => step(1)} disabled={lessonIndex === lessons.length - 1}>next</Button>
      <Button variant="outline" size="sm" onclick={toggleSolve} disabled={!hasSolution} data-testid="solve-button">
        {completed ? 'reset' : 'solve'}
      </Button>
    </div>
  </header>

  <div class="flex-1 min-h-0 flex">
    <!-- Lesson sidebar -->
    <nav
      class="overflow-hidden bg-surface border border-border rounded-[14px] shadow-app flex-shrink-0 min-h-0"
      style="width: {sidebarOpen ? '220px' : '0'}; margin-right: {sidebarOpen ? '0.7rem' : '0'}; opacity: {sidebarOpen ? '1' : '0'}; border-width: {sidebarOpen ? '1px' : '0'}; transition: width 0.2s ease, margin-right 0.2s ease, opacity 0.15s ease"
    >
      <div bind:this={sidebarInnerEl} class="w-[220px] h-full overflow-y-auto p-2 flex flex-col">
        {#each parts as part, pi}
          {#if pi > 0}<div class="border-t border-border mx-1 my-2"></div>{/if}
          <div class="text-[0.6rem] font-bold uppercase tracking-widest text-muted-foreground px-2 py-[0.3rem] mt-1 select-none">
            {part.title}
          </div>
          {#each part.chapters as chapter}
            <button
              class="w-full flex items-center justify-between px-2 py-[0.28rem] rounded-[7px] transition-colors hover:bg-surface-2 text-left mt-[0.15rem]"
              on:click={() => toggleChapter(chapter.title)}
            >
              <span class="text-[0.71rem] text-muted-foreground italic">{chapter.title}</span>
              <span class="text-[0.6rem] text-muted-foreground opacity-60 ml-1 flex-shrink-0">
                {expandedChapters.has(chapter.title) ? '▾' : '▸'}
              </span>
            </button>
            {#if expandedChapters.has(chapter.title)}
              {#each chapter.lessons as item}
                {@const idx = lessons.findIndex(l => l.slug === item.slug)}
                <button
                  class="w-full text-left text-[0.79rem] pl-[1.1rem] pr-2 py-[0.22rem] rounded-[7px] transition-colors leading-snug {idx === lessonIndex ? 'bg-tab-selected-bg text-teal font-medium' : 'text-foreground hover:bg-surface-2'}"
                  data-active={idx === lessonIndex}
                  on:click={() => { lessonIndex = idx; ensureChapterVisible(idx); }}
                >
                  {idx + 1}. {item.title}
                </button>
              {/each}
            {/if}
          {/each}
        {/each}
      </div>
    </nav>

    <section class="flex-1 min-h-0 flex max-narrow:flex-col">
    <article style="flex: 0 0 {hSplit}%; min-width: 200px"
             class="bg-surface border border-border rounded-[14px] shadow-app min-h-0 flex flex-col p-[0.9rem] gap-3 overflow-y-auto [scrollbar-gutter:stable]">
      <h2 class="m-0 text-[1.15rem] font-bold leading-tight text-foreground">{lesson.title}</h2>
      <div class="lesson-body">
        {@html lesson.html}
      </div>
    </article>

    <!-- Horizontal drag handle — hidden on narrow -->
    <div role="separator" aria-label="Resize panels" aria-orientation="vertical"
         class="max-narrow:hidden flex-none w-[0.7rem] flex items-center justify-center cursor-col-resize select-none group"
         style="touch-action:none"
         on:pointerdown={startHResize}>
      <div class="w-[2px] h-8 rounded-full bg-border group-hover:bg-teal transition-colors"></div>
    </div>

    <section style="flex: 1 1 0%; min-width: 300px" class="min-h-0 flex flex-col">

      <!-- Editor pane -->
      <div style="flex: 0 0 {vSplit}%; min-height: 150px"
           class="bg-surface border border-border rounded-[14px] shadow-app min-h-0 overflow-hidden grid grid-rows-[auto_1fr]">
        <div class="px-[0.5rem] pt-[0.4rem] pb-[0.3rem] overflow-x-auto">
          <Tabs value={selectedFile} onValueChange={(v) => (selectedFile = v)}>
            <TabsList class="h-auto flex-nowrap gap-[0.35rem] bg-transparent p-0 w-max">
              {#each Object.keys(workspace) as filename}
                <TabsTrigger
                  value={filename}
                  class="font-mono text-[0.8rem] rounded-[10px] border border-border data-[state=active]:border-teal data-[state=active]:text-teal data-[state=active]:bg-tab-selected-bg data-[state=inactive]:bg-surface-2"
                >
                  {filename}
                </TabsTrigger>
              {/each}
            </TabsList>
          </Tabs>
        </div>

        <CodeEditor value={workspace[selectedFile] || ''} onchange={onEdit} />
      </div>

      <!-- Vertical drag handle -->
      <div role="separator" aria-label="Resize panels" aria-orientation="horizontal"
           class="flex-none h-[0.7rem] flex items-center justify-center cursor-row-resize select-none group"
           style="touch-action:none"
           on:pointerdown={startVResize}>
        <div class="h-[2px] w-8 rounded-full bg-border group-hover:bg-teal transition-colors"></div>
      </div>

      <!-- Runtime pane -->
      <div style="flex: 1 1 0%; min-height: 220px"
           class="bg-surface border border-border rounded-[14px] shadow-app min-h-0 overflow-hidden flex flex-col">

        <!-- Header: tab switcher + action buttons -->
        <div class="flex justify-between items-center gap-[0.7rem] px-[0.5rem] py-[0.35rem]">
          {#if hasWaveform}
            <Tabs value={activeRuntimeTab} onValueChange={(v) => (activeRuntimeTab = v)}>
              <TabsList class="h-auto gap-[0.35rem] bg-transparent p-0">
                <TabsTrigger value="logs" data-testid="runtime-tab-logs"
                  class="text-[0.8rem] rounded-[10px] border border-border data-[state=active]:border-teal data-[state=active]:text-teal data-[state=active]:bg-tab-selected-bg data-[state=inactive]:bg-surface-2">
                  Logs
                </TabsTrigger>
                <TabsTrigger value="waves" data-testid="runtime-tab-waves"
                  class="text-[0.8rem] rounded-[10px] border border-border data-[state=active]:border-teal data-[state=active]:text-teal data-[state=active]:bg-tab-selected-bg data-[state=inactive]:bg-surface-2">
                  Waves
                </TabsTrigger>
              </TabsList>
            </Tabs>
          {:else}
            <div></div>
          {/if}

          <div class="flex gap-[0.4rem]">
            {#if lesson.runner !== 'bmc' && lesson.runner !== 'lec'}
              <Button variant="outline" size="sm" onclick={() => runSim('sim')} disabled={running} data-testid="run-button">
                {#if running && runMode === 'sim'}
                  {runPhase === 'running' ? (lesson.runner === 'cocotb' ? 'testing...' : 'running...') : 'compiling...'}
                {:else}
                  {lesson.runner === 'cocotb' ? 'test' : 'run'}
                {/if}
              </Button>
            {/if}
            {#if lesson.runner === 'bmc' || lesson.runner === 'both'}
              <Button variant="outline" size="sm" onclick={() => runSim('bmc')} disabled={running} data-testid="verify-button">
                {#if running && runMode === 'bmc'}
                  {runPhase === 'running' ? 'verifying...' : 'compiling...'}
                {:else}
                  verify
                {/if}
              </Button>
            {/if}
            {#if lesson.runner === 'lec'}
              <Button variant="outline" size="sm" onclick={() => runSim('lec')} disabled={running} data-testid="verify-button">
                {#if running && runMode === 'lec'}
                  {runPhase === 'running' ? 'verifying...' : 'compiling...'}
                {:else}
                  verify (LEC)
                {/if}
              </Button>
            {/if}
          </div>
        </div>

        <!-- Logs tab content -->
        <div
          data-testid="runtime-logs"
          class="m-0 bg-logs-bg text-logs-text p-[0.6rem] overflow-auto font-mono text-[0.78rem]
                 {activeRuntimeTab === 'waves' ? 'hidden' : 'flex-1 min-h-0'}"
        >
          {#if logs.length === 0}
            <div class="text-muted-foreground">no output yet</div>
          {:else}
            <div class="flex flex-col gap-2">
              {#each logs as entry}
                {#if isStdoutEntry(entry)}
                  <details open>
                    <summary class="cursor-pointer select-none text-logs-text">stdout</summary>
                    <pre class="m-0 mt-1 whitespace-pre-wrap break-words">{stripStreamPrefix(entry)}</pre>
                  </details>
                {:else if isStderrEntry(entry)}
                  <details open>
                    <summary class="cursor-pointer select-none text-logs-text">stderr</summary>
                    <pre class="m-0 mt-1 whitespace-pre-wrap break-words">{stripStreamPrefix(entry)}</pre>
                  </details>
                {:else}
                  <div class="whitespace-pre-wrap break-words">{entry}</div>
                {/if}
              {/each}
            </div>
          {/if}
        </div>

        <!-- Waves tab content — always mounted so Surfer doesn't reload on tab switch -->
        {#if hasWaveform}
          <div class="{activeRuntimeTab === 'waves' ? 'flex-1 min-h-0' : 'hidden'}">
            <WaveformViewer
              vcd={lastWaveform.text}
              hasRun={hasRunOnce}
            />
          </div>
        {/if}
      </div>

    </section>
  </section>
  </div>

  {#if showCopyModal}
    <!-- svelte-ignore a11y-click-events-have-key-events a11y-no-static-element-interactions -->
    <div class="fixed inset-0 bg-black/50 flex items-center justify-center z-50"
         on:click|self={onCopyModalOk}>
      <div class="bg-surface rounded-[14px] shadow-xl p-8 max-w-[440px] mx-4 flex flex-col gap-4 border border-border">
        <h2 class="m-0 text-[1.2rem] font-semibold leading-snug">Copy is currently disabled!</h2>
        <p class="m-0 text-[0.88rem] text-muted-foreground leading-relaxed">
          We recommend typing the code into the editor to complete each exercise,
          as this results in better retention and understanding.
        </p>
        <label class="flex items-center gap-2 text-[0.87rem] cursor-pointer select-none">
          <input type="checkbox" bind:checked={copyEnableChecked} class="w-4 h-4 accent-teal" />
          enable copy for the duration of this session
        </label>
        <button
          on:click={onCopyModalOk}
          class="self-start px-6 py-[0.45rem] bg-teal text-white rounded-[8px] font-medium text-[0.9rem] hover:opacity-90 transition-opacity"
        >OK</button>
      </div>
    </div>
  {/if}
</main>
