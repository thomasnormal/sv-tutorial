export function classifySmtOutput(output) {
  const lines = String(output ?? '').trim().split(/\r?\n/).map((line) => line.trim()).filter(Boolean);
  const statuses = lines.filter((line) => line === 'sat' || line === 'unsat');
  const hasSat = statuses.includes('sat');
  const allUnsat = statuses.length > 0 && statuses.every((line) => line === 'unsat');

  if (allUnsat) return { status: 'proved', ok: true, lines };
  if (hasSat) return { status: 'counterexample', ok: false, lines };
  return { status: 'unknown', ok: false, lines };
}

export function addModelQuery(smtlibText) {
  const resetIndex = smtlibText.lastIndexOf('(reset)');
  return resetIndex >= 0
    ? `${smtlibText.slice(0, resetIndex)}(get-model)\n${smtlibText.slice(resetIndex)}`
    : `${smtlibText}\n(get-model)\n`;
}

function decodeBitVector(widthText, valueText) {
  const width = Number(widthText);
  const raw = valueText.startsWith('#x')
    ? BigInt(`0x${valueText.slice(2)}`)
    : BigInt(`0b${valueText.slice(2)}`);
  if (width % 2 !== 0) return raw.toString();

  const half = BigInt(width / 2);
  const mask = (1n << half) - 1n;
  if ((raw & mask) !== 0n) return valueText;
  return ((raw >> half) & mask).toString();
}

export function parseModelAssignments(modelOutput, { skipInternal = true } = {}) {
  const modelFlat = String(modelOutput ?? '').replace(/\s+/g, ' ');
  const assignments = [];
  const bitVector = /\(define-fun\s+(?:\|([^|]+)\||([^\s()]+))\s+\(\)\s+\(_\s+BitVec\s+(\d+)\)\s+(#x[0-9a-fA-F]+|#b[01]+)\s*\)/g;
  const bool = /\(define-fun\s+(?:\|([^|]+)\||([^\s()]+))\s+\(\)\s+Bool\s+(true|false)\s*\)/g;
  let match;

  while ((match = bitVector.exec(modelFlat)) !== null) {
    const name = match[1] ?? match[2];
    if (skipInternal && /^c\d+_/.test(name)) continue;
    assignments.push({ name, value: decodeBitVector(match[3], match[4]), raw: match[4] });
  }

  while ((match = bool.exec(modelFlat)) !== null) {
    const name = match[1] ?? match[2];
    if (skipInternal && /^c\d+_/.test(name)) continue;
    assignments.push({ name, value: match[3] === 'true' ? '1' : '0', raw: match[3] });
  }

  return assignments;
}
