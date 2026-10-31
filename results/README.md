# Matrix result history

Every `*.md` file in this directory is a complete run/verify matrix for one
Mox build. The filename is the Mox commit SHA, and the table records the raw
browser status and diagnostic for every case. `scripts/generate-lesson-status.mjs`
uses the two newest tables for the status page's **What changed** section;
`scripts/matrix-diff.sh` compares any two tables directly.

The first entry is the item-18 baseline reconstructed from its durable census.
Future entries are written by `scripts/run-matrix.sh`.
