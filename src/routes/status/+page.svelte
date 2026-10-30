<script>
  import { base } from '$app/paths';

  let { data } = $props();
  const statusClass = (status) => status === 'PASS'
    ? 'border-teal/40 bg-teal/10 text-teal'
    : status === 'Mox refusal'
      ? 'border-amber-400/50 bg-amber-400/10 text-amber-700 dark:text-amber-300'
      : 'border-sky-400/50 bg-sky-400/10 text-sky-700 dark:text-sky-300';
  const displayStatus = (status) => status === 'environment' ? 'Environment' : status;
</script>

<svelte:head>
  <title>Lesson status – SV Tutorial</title>
  <meta name="description" content="Current browser status for every SystemVerilog tutorial lesson." />
</svelte:head>

<main data-testid="status-page" class="flex-1 min-h-0 overflow-y-auto p-4 md:p-7">
  <div class="mx-auto max-w-6xl flex flex-col gap-5">
    <div class="flex flex-wrap items-start justify-between gap-3">
      <div>
        <a href={base || '/'} class="text-[0.8rem] text-muted-foreground hover:text-teal">← Back to tutorial</a>
        <h1 class="mt-2 text-[1.6rem] font-bold text-foreground">Lesson status</h1>
        <p class="mt-1 max-w-3xl text-[0.9rem] leading-relaxed text-muted-foreground">
          This page is generated from the browser census during every build. A Mox refusal is a
          language or runtime capability gap; an environment status identifies a worker or library
          gap. PASS means the published WASM path completed its check.
        </p>
      </div>
      <div class="flex flex-wrap gap-2 text-[0.78rem]" data-testid="status-summary">
        {#each [['PASS', data.statusSummary.PASS], ['Mox refusal', data.statusSummary['Mox refusal']], ['Environment', data.statusSummary.environment], ['Tutorial', data.statusSummary.tutorial]] as [label, count]}
          <span class="rounded-full border px-2.5 py-1 {statusClass(label === 'Environment' ? 'environment' : label)}">
            {label}: {count}
          </span>
        {/each}
      </div>
    </div>

    <div class="overflow-x-auto rounded-[12px] border border-border bg-surface shadow-app">
      <table class="w-full min-w-[760px] border-collapse text-left text-[0.82rem]">
        <thead class="bg-surface-2 text-[0.72rem] uppercase tracking-[0.08em] text-muted-foreground">
          <tr>
            <th class="px-3 py-2.5">Lesson</th>
            <th class="px-3 py-2.5">Construct</th>
            <th class="px-3 py-2.5">IEEE clause</th>
            <th class="px-3 py-2.5">Current status</th>
            <th class="px-3 py-2.5">Diagnostic</th>
          </tr>
        </thead>
        <tbody>
          {#each data.lessonStatuses as lesson}
            {#each lesson.rows as row, rowIndex}
              <tr id={rowIndex === 0 ? lesson.slug.replace('/', '-') : undefined} class="border-t border-border align-top" data-testid="status-row">
                <td class="px-3 py-3 font-medium">
                  <a class="text-foreground hover:text-teal" href="{base}/lesson/{lesson.slug}">{lesson.title}</a>
                  <div class="mt-0.5 text-[0.7rem] text-muted-foreground">{lesson.slug} · {row.mode}</div>
                </td>
                <td class="px-3 py-3 text-muted-foreground">{row.construct}</td>
                <td class="px-3 py-3 text-muted-foreground">{row.clause}</td>
                <td class="px-3 py-3">
                  <span class="inline-flex rounded-full border px-2 py-0.5 text-[0.72rem] font-medium {statusClass(row.status)}">
                    {displayStatus(row.status)}
                  </span>
                </td>
                <td class="px-3 py-3 font-mono text-[0.72rem] text-muted-foreground">{row.diagnostic || '—'}</td>
              </tr>
            {/each}
          {/each}
        </tbody>
      </table>
    </div>
  </div>
</main>
