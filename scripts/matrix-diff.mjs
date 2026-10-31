#!/usr/bin/env node

import { computeMatrixDiff, readResultTable } from './matrix-results.mjs';

const [oldPath, newPath] = process.argv.slice(2);
if (!oldPath || !newPath) {
  console.error('usage: scripts/matrix-diff.sh <old-results> <new-results>');
  process.exit(2);
}

const oldTable = readResultTable(oldPath);
const newTable = readResultTable(newPath);
const diff = computeMatrixDiff(oldTable, newTable);
const oldLabel = oldTable.sha || oldPath;
const newLabel = newTable.sha || newPath;

console.log(`# Matrix diff: ${oldLabel} → ${newLabel}`);
console.log('');
console.log('## PASS ↔ FAIL moves');
if (!diff.moves.length) {
  console.log('None.');
} else {
  for (const row of diff.moves) {
    const diagnostic = row.newDiagnostic || row.oldDiagnostic;
    console.log(`- \`${row.slug}\` (${row.mode}): ${row.oldVerdict} → ${row.newVerdict}${diagnostic ? ` — ${diagnostic}` : ''}`);
  }
}
console.log('');
console.log('## Mox diagnostic changes');
if (!diff.diagnosticChanges.length) {
  console.log('None.');
} else {
  for (const row of diff.diagnosticChanges) {
    console.log(`- \`${row.slug}\` (${row.mode}): ${row.oldDiagnostic || '—'} → ${row.newDiagnostic || '—'}`);
  }
}
