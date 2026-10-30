# Contributing

Thanks for improving the SystemVerilog, SVA, and UVM tutorial. Keep each change
small enough to review and leave the lesson, its tests, and the curriculum
tracker in a consistent state.

## Set up the repository

Use Node 22 and the versions recorded in [`scripts/toolchain.lock.sh`](scripts/toolchain.lock.sh).
The normal setup is:

```bash
npm ci
scripts/setup-surfer.sh
npm run setup:pyodide
npm run setup:mox
```

Use `npm run check:req` for the frontend prerequisites and
`npm run check:req:wasm` after activating the pinned Emscripten 4.0.21 toolchain.
The Mox checkout must match both the locked Mox commit and its LLVM submodule
commit. Do not silently replace a pinned commit with a moving branch; a pin
bump needs a reproducible build result and a note in `docs/mox-bugs/` when a
failure prevents the artifacts from being generated.

## Work on a lesson

1. Read [`CURRICULUM.md`](CURRICULUM.md), [`RUBRIC.md`](RUBRIC.md), and the
   neighboring lessons before choosing a slug or changing its prerequisites.
2. Keep the lesson's starter source, solution source, description, and
   self-checking testbench together under `src/lessons/`. Update the lesson
   catalog and metadata when the lesson is new, and keep the starter visibly
   incomplete while the solution produces a labelled `PASS`.
3. Run the lesson's native or interpreter check when available, then run its
   focused browser test. Record the rubric score and any flags in
   `CURRICULUM.md`; a finished lesson must score at least 2 on every rubric
   dimension.
4. Update `README.md` or other docs when the workflow, prerequisites, or
   published curriculum changes.

Generated Mox and Surfer assets are local build outputs. Keep them out of
commits unless a release process explicitly asks for an artifact update.

## Validate a change

Run the checks that cover the files you changed:

```bash
git diff --check
npm test
npm run build
npm run test:e2e
```

For a lesson-only change, a focused Playwright command is acceptable during
iteration, but the pull request should name the focused command and its result.
If the Mox WASM artifacts are unavailable, report that runtime limitation
explicitly instead of replacing the simulator with a mock.

WASM builds are resource-intensive. Use the repository build script with no
more than eight Ninja jobs and a 20 GB virtual-memory limit when running a
full build, and keep only one heavy build active at a time. The script's
`MOX_WASM_JOBS`, `MOX_WASM_MEMORY_LIMIT_KB`, and timeout variables make those
limits explicit.

## Branches and pull requests

Start from an up-to-date `main` branch and use a descriptive branch for one
lesson or documentation item, for example `fleet/<topic>`. Keep unrelated
refactors out of the branch. Commits should explain the user-visible change;
the pull request should include the tests run, their results, the rubric score
for changed lessons, and any known runtime limitation.

Push the feature branch and open a pull request against `main`. Never push
directly to `main`; the maintainer reviews and merges pull requests.

