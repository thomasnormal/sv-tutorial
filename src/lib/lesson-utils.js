export function cloneFiles(files) {
  return JSON.parse(JSON.stringify(files));
}

export function mergeFiles(a, b) {
  return { ...cloneFiles(a), ...cloneFiles(b) };
}

export function normalize(text) {
  return String(text).replace(/\s+/g, ' ').trim();
}

export function filesEqual(a, b) {
  const aKeys = Object.keys(a).sort();
  const bKeys = Object.keys(b).sort();
  if (aKeys.length !== bKeys.length) return false;
  for (let i = 0; i < aKeys.length; i++) {
    const aKey = aKeys[i];
    const bKey = bKeys[i];
    if (aKey !== bKey) return false;
    if (normalize(a[aKey]) !== normalize(b[bKey])) return false;
  }
  return true;
}

export function topNameFromFocus(path) {
  const filename = path.split('/').pop() || 'top.sv';
  return filename.replace(/\.[^.]+$/, '');
}
