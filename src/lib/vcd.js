// Parse VCD and return { id, name, fullPath } for the variable with the EARLIEST
// first transition after the initial $dumpvars block (ignoring pure-initialization
// changes).  Ties broken by VCD declaration order.  Returns null if no signal
// transitions at all.
//
// fullPath is the dot-joined scope hierarchy required by Surfer's id_of_name()
// (e.g. "tb.req", not just "req").
export function firstTransitioningVar(vcdText) {
  // Collect {id (identifier code), name, fullPath} in declaration order,
  // tracking the scope stack to build the full dot-path for each variable.
  const vars = [];
  const scopeStack = [];
  const headerText = vcdText.slice(0, Math.max(0, vcdText.search(/\$enddefinitions\b/)));
  const tokenRe = /\$scope\s+\w+\s+(\w+)\s*\$end|\$upscope\s*\$end|\$var\s+\w+\s+\d+\s+(\S+)\s+(\S+)[^$]*\$end/g;
  for (const m of headerText.matchAll(tokenRe)) {
    if (m[0].startsWith('$scope')) {
      scopeStack.push(m[1]);
    } else if (m[0].startsWith('$upscope')) {
      scopeStack.pop();
    } else {
      // $var — m[2]=identifier code, m[3]=leaf name
      vars.push({ id: m[2], name: m[3], fullPath: [...scopeStack, m[3]].join('.') });
    }
  }
  if (vars.length === 0) return null;

  // Find $enddefinitions and skip past the $dumpvars initial-state block.
  const enddefs = vcdText.search(/\$enddefinitions\b/);
  if (enddefs === -1) return null;
  let rest = vcdText.slice(enddefs);
  // Changes that follow the $dumpvars block happen at the dump time: the
  // last timestamp before the block ends (Mox writes it inside the block).
  let dumpTime = -1;
  const dumpStart = rest.indexOf('$dumpvars');
  if (dumpStart !== -1) {
    const dumpEnd = rest.indexOf('$end', dumpStart);
    if (dumpEnd !== -1) {
      const lastTime = [...rest.slice(0, dumpEnd).matchAll(/^\s*#(\d+)/gm)].pop();
      if (lastTime) dumpTime = parseInt(lastTime[1], 10);
      rest = rest.slice(dumpEnd + 4);
    }
  }

  // Walk timestamps one by one; for each timestamp collect which identifiers
  // change.  Track the first timestamp at which each identifier changes.
  // We stop once every declared identifier has been seen at least once (to
  // avoid scanning the entire VCD on large traces).
  const firstChangeAt = new Map(); // id → first timestamp with a value change
  let currentTime = dumpTime;
  const lines = rest.split('\n');
  let unseen = new Set(vars.map((v) => v.id));

  for (const line of lines) {
    if (unseen.size === 0) break;
    const trimmed = line.trim();
    if (trimmed.startsWith('#')) {
      currentTime = parseInt(trimmed.slice(1), 10);
      continue;
    }
    if (currentTime < 0) continue;
    const m = trimmed.match(/^[01xzXZ]([!-~]+)|^b[01xzXZ]+\s+([!-~]+)/);
    if (m) {
      const id = m[1] ?? m[2];
      if (!firstChangeAt.has(id)) firstChangeAt.set(id, currentTime);
      unseen.delete(id);
    }
  }

  if (firstChangeAt.size === 0) return null;

  // Return the var with the smallest first-change timestamp (ties → first
  // in declaration order, which is the natural loop order over vars).
  let best = null;
  let bestTime = Infinity;
  for (const v of vars) {
    const t = firstChangeAt.get(v.id);
    if (t !== undefined && t < bestTime) {
      bestTime = t;
      best = v;
    }
  }
  return best;
}
