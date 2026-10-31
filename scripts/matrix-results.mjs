import { existsSync, readFileSync, readdirSync, statSync } from 'node:fs';
import { resolve } from 'node:path';

export function splitMarkdownRow(line) {
  if (!line.startsWith('|')) return [];
  const body = line.endsWith('|') ? line.slice(1, -1) : line.slice(1);
  const cells = [];
  let cell = '';
  let escaped = false;
  for (const character of body) {
    if (escaped) {
      cell += character;
      escaped = false;
    } else if (character === '\\') {
      cell += character;
      escaped = true;
    } else if (character === '|') {
      cells.push(cell.trim());
      cell = '';
    } else {
      cell += character;
    }
  }
  cells.push(cell.trim());
  return cells;
}

function cleanCell(value) {
  return value.trim().replace(/^`([\s\S]*)`$/, '$1').replaceAll('\\|', '|');
}

export function parseResultTable(markdown, source = '') {
  const metadata = {};
  for (const line of markdown.split(/\r?\n/)) {
    const match = line.match(/^- ([A-Za-z][A-Za-z _-]*):\s*(.*)$/);
    if (match) metadata[match[1].trim().toLowerCase().replaceAll(' ', '_')] = match[2].trim();
  }
  const rows = [];
  for (const line of markdown.split(/\r?\n/)) {
    if (!line.startsWith('| `')) continue;
    const cells = splitMarkdownRow(line).map(cleanCell);
    if (cells.length !== 4 || !cells[0].includes('/')) continue;
    const [slug, mode, status, diagnostic] = cells;
    rows.push({ slug, mode, status: status || 'FAIL', diagnostic });
  }
  return {
    source,
    sha: metadata['mox_build']?.replace(/^`|`$/g, '') || source.split('/').pop()?.replace(/\.md$/, '') || '',
    generatedAt: metadata.generated ? new Date(metadata.generated).toISOString() : null,
    summary: metadata.matrix || '',
    artifactSource: metadata.artifact_source || '',
    rows,
    byCase: new Map(rows.map((row) => [`${row.slug}\0${row.mode}`, row]))
  };
}

export function readResultTable(filePath) {
  return parseResultTable(readFileSync(filePath, 'utf8'), filePath);
}

export function recentResultTables(resultsDir, limit = 2) {
  if (!existsSync(resultsDir)) return [];
  return readdirSync(resultsDir)
    .filter((name) => name.endsWith('.md') && name !== 'README.md')
    .map((name) => readResultTable(resolve(resultsDir, name)))
    .sort((a, b) => {
      const at = a.generatedAt ? Date.parse(a.generatedAt) : statSync(a.source).mtimeMs;
      const bt = b.generatedAt ? Date.parse(b.generatedAt) : statSync(b.source).mtimeMs;
      return bt - at;
    })
    .slice(0, limit);
}

function verdict(status) {
  return status === 'PASS' ? 'PASS' : 'FAIL';
}

export function computeMatrixDiff(oldTable, newTable) {
  const moves = [];
  const diagnosticChanges = [];
  const keys = new Set([...oldTable.byCase.keys(), ...newTable.byCase.keys()]);
  for (const key of [...keys].sort()) {
    const oldRow = oldTable.byCase.get(key);
    const newRow = newTable.byCase.get(key);
    if (!oldRow || !newRow) continue;
    const oldVerdict = verdict(oldRow.status);
    const newVerdict = verdict(newRow.status);
    const row = {
      slug: newRow.slug,
      mode: newRow.mode,
      oldStatus: oldRow.status,
      newStatus: newRow.status,
      oldVerdict,
      newVerdict,
      oldDiagnostic: oldRow.diagnostic || '',
      newDiagnostic: newRow.diagnostic || ''
    };
    if (oldVerdict !== newVerdict) moves.push(row);
    const moxDiagnostic = oldRow.status === 'Mox refusal' || newRow.status === 'Mox refusal';
    if (moxDiagnostic && oldRow.diagnostic !== newRow.diagnostic && (oldRow.diagnostic || newRow.diagnostic)) {
      diagnosticChanges.push(row);
    }
  }
  return { moves, diagnosticChanges };
}

