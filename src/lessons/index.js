// Auto-discovered lesson content — no per-lesson index.js needed.
// To add a lesson: create src/lessons/<part>/<slug>/ with meta.json,
// description.html, *.sv (starter), *.sol.sv (solution), then add the
// slug to the structure below.

const htmls     = import.meta.glob('./*/*/description.html',                              { query: '?raw', import: 'default', eager: true });
const starters  = import.meta.glob(['./*/*/*.{sv,py}', '!./*/*/*.sol.sv'],               { query: '?raw', import: 'default', eager: true });
const solutions = import.meta.glob('./*/*/*.sol.sv',                                      { query: '?raw', import: 'default', eager: true });
const metas     = import.meta.glob('./*/*/meta.json',                      { eager: true,   import: 'default' });

function buildLessonMap() {
  const map = {};
  const entry = (slug) => { map[slug] ??= { files: { a: {}, b: {} } }; return map[slug]; };

  for (const [path, html] of Object.entries(htmls)) {
    const [, p, l] = path.match(/^\.\/([\w-]+)\/([\w-]+)\//);
    entry(`${p}/${l}`).html = html;
  }

  for (const [path, meta] of Object.entries(metas)) {
    const [, p, l] = path.match(/^\.\/([\w-]+)\/([\w-]+)\//);
    const slug = `${p}/${l}`;
    Object.assign(entry(slug), { slug, ...meta });
  }

  for (const [path, content] of Object.entries(starters)) {
    const [, p, l, file] = path.match(/^\.\/([\w-]+)\/([\w-]+)\/(.+\.(sv|py))$/);
    entry(`${p}/${l}`).files.a[`/src/${file}`] = content;
  }

  for (const [path, content] of Object.entries(solutions)) {
    const [, p, l, stem] = path.match(/^\.\/([\w-]+)\/([\w-]+)\/(.+)\.sol\.sv$/);
    entry(`${p}/${l}`).files.b[`/src/${stem}.sv`] = content;
  }

  return map;
}

const lessonMap = buildLessonMap();
const L = (slug) => lessonMap[slug];

// ── Hierarchy ─────────────────────────────────────────────────────────────────
export const parts = [
  {
    title: 'SystemVerilog Basics',
    chapters: [
      { title: 'Introduction',          lessons: [L('sv/welcome'), L('sv/modules-and-ports')] },
      { title: 'Combinational Logic',   lessons: [L('sv/always-comb'), L('sv/priority-enc')] },
      { title: 'Sequential Logic',      lessons: [L('sv/always-ff'), L('sv/counter')] },
      { title: 'Parameterized Modules', lessons: [L('sv/parameters')] },
      { title: 'Interfaces & Procedures', lessons: [L('sv/interfaces'), L('sv/tasks-functions')] },
      { title: 'State Machines',        lessons: [L('sv/enums'), L('sv/fsm')] },
    ],
  },
  {
    title: 'SystemVerilog Assertions',
    chapters: [
      { title: 'Your First Assertion',      lessons: [L('sva/immediate-assert'), L('sva/sequence-basics')] },
      { title: 'Clock Delay & Sequences',   lessons: [L('sva/clock-delay'), L('sva/consecutive-rep'), L('sva/nonconsec-rep')] },
      { title: 'Properties & Implication',  lessons: [L('sva/implication'), L('sva/req-ack'), L('sva/disable-iff'), L('sva/vacuous-pass')] },
      { title: 'Sampled Value Functions',   lessons: [L('sva/rose-fell'), L('sva/stable-past')] },
      { title: 'Coverage',                  lessons: [L('sva/cover-property')] },
      { title: 'Advanced Properties',       lessons: [L('sva/local-vars'), L('sva/onehot')] },
      { title: 'Formal Verification',       lessons: [L('sva/formal-intro'), L('sva/formal-assume'), L('sva/lec')] },
    ],
  },
  {
    title: 'Universal Verification Methodology',
    chapters: [
      { title: 'UVM Foundations', lessons: [L('uvm/reporting'), L('uvm/seq-item')] },
      { title: 'Stimulus',        lessons: [L('uvm/sequence'), L('uvm/driver')] },
      { title: 'Checking',        lessons: [L('uvm/monitor'), L('uvm/env')] },
      {
        title: 'Functional Coverage',
        lessons: [L('uvm/covergroup'), L('uvm/cross-coverage'), L('uvm/coverage-driven')],
      },
    ],
  },
  {
    title: 'cocotb',
    chapters: [
      { title: 'cocotb Basics', lessons: [L('cocotb/first-test'), L('cocotb/clock-and-timing')] },
    ],
  },
];

export const lessons = parts.flatMap((part) =>
  part.chapters.flatMap((chapter) =>
    chapter.lessons.map((lesson) => ({
      ...lesson,
      partTitle: part.title,
      chapterTitle: chapter.title,
    }))
  )
);
