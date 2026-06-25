#!/usr/bin/env bash
set -euo pipefail

PUBLISH=0
POSITIONAL=()
for arg in "$@"; do
  case "$arg" in
    --publish) PUBLISH=1 ;;
    *) POSITIONAL+=("$arg") ;;
  esac
done

SRC_DIR="${POSITIONAL[0]:-vendor/mox/build-wasm/bin}"
DST_DIR="${POSITIONAL[1]:-static/mox}"
UVM_SRC_DIR="${POSITIONAL[2]:-vendor/mox/lib/Runtime/uvm-core/src}"
UVM_DST_DIR="$DST_DIR/uvm-core/src"
UVM_MANIFEST_PATH="$DST_DIR/uvm-core/uvm-manifest.json"

TOOLS=("mox-bmc" "mox-sim" "mox-verilog" "mox-lec")
# VPI-capable sim is a separate build target (Asyncify + VPI exports).
# It is optional — warn if missing but do not abort.
VPI_TOOL="mox-sim-vpi"
missing=()

for tool in "${TOOLS[@]}"; do
  if [ ! -f "$SRC_DIR/$tool.js" ]; then
    missing+=("$tool.js")
  fi
  if [ ! -f "$SRC_DIR/$tool.wasm" ]; then
    missing+=("$tool.wasm")
  fi
done

if [ "${#missing[@]}" -ne 0 ]; then
  echo "Missing MOX wasm artifacts in $SRC_DIR" >&2
  echo "Missing files: ${missing[*]}" >&2
  exit 1
fi

mkdir -p "$DST_DIR"
for tool in "${TOOLS[@]}"; do
  cp -f "$SRC_DIR/$tool.js" "$DST_DIR/$tool.js"
  cp -f "$SRC_DIR/$tool.wasm" "$DST_DIR/$tool.wasm"
done

patch_callmain_export() {
  local js_path="$1"
  node - "$js_path" <<'NODE'
const fs = require('fs');

const jsPath = process.argv[2];
let source = fs.readFileSync(jsPath, 'utf8');

if (
  source.includes('__svt_callMain')
) {
  console.log(`Skipped callMain shim patch (already present): ${jsPath}`);
  process.exit(0);
}

if (!source.includes('function callMain(')) {
  console.log(`Skipped callMain patch (no callMain symbol): ${jsPath}`);
  process.exit(0);
}

source += '\n;try{if(typeof callMain==="function"&&typeof self!=="undefined"&&typeof self.__svt_callMain!=="function"){self.__svt_callMain=callMain;}}catch(_){}\n';
fs.writeFileSync(jsPath, source);
console.log(`Patched callMain shim in ${jsPath}`);
NODE
}

for tool in "${TOOLS[@]}"; do
  patch_callmain_export "$DST_DIR/$tool.js"
done

# Sync VPI-capable sim. mox-sim already includes Asyncify + VPI exports
# unconditionally in Emscripten builds, so use it as the VPI binary when a
# separately-named mox-sim-vpi build is not present in the source dir.
if [ -f "$SRC_DIR/$VPI_TOOL.js" ] && [ -f "$SRC_DIR/$VPI_TOOL.wasm" ]; then
  cp -f "$SRC_DIR/$VPI_TOOL.js" "$DST_DIR/$VPI_TOOL.js"
  cp -f "$SRC_DIR/$VPI_TOOL.wasm" "$DST_DIR/$VPI_TOOL.wasm"
elif [ -f "$SRC_DIR/mox-sim.js" ] && [ -f "$SRC_DIR/mox-sim.wasm" ]; then
  echo "Note: $VPI_TOOL not in $SRC_DIR — using mox-sim as VPI-capable fallback" >&2
  cp -f "$SRC_DIR/mox-sim.js" "$DST_DIR/$VPI_TOOL.js"
  cp -f "$SRC_DIR/mox-sim.wasm" "$DST_DIR/$VPI_TOOL.wasm"
else
  echo "Note: $VPI_TOOL not found and no mox-sim fallback — skipping (cocotb lessons will be unavailable)" >&2
  HAVE_VPI=0
fi
if [ "${HAVE_VPI:-}" != "0" ]; then
  patch_callmain_export "$DST_DIR/$VPI_TOOL.js"
  HAVE_VPI=1
fi

if [ ! -d "$UVM_SRC_DIR" ]; then
  echo "Missing full UVM source directory: $UVM_SRC_DIR" >&2
  exit 1
fi

mkdir -p "$UVM_DST_DIR"
rsync -a --delete \
  --include='*/' \
  --include='*.sv' \
  --include='*.svh' \
  --exclude='*' \
  "$UVM_SRC_DIR/" "$UVM_DST_DIR/"

node - "$UVM_DST_DIR" "$UVM_MANIFEST_PATH" <<'NODE'
const fs = require('fs');
const path = require('path');

const srcDir = process.argv[2];
const outFile = process.argv[3];

function walk(dir, acc = []) {
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const abs = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      walk(abs, acc);
      continue;
    }
    if (!entry.isFile()) continue;
    if (!/\.(sv|svh)$/i.test(entry.name)) continue;
    acc.push(path.relative(srcDir, abs).split(path.sep).join('/'));
  }
  return acc;
}

const files = walk(srcDir).sort();
const manifest = {
  rootPath: '/mox/uvm-core/src',
  files
};

fs.mkdirSync(path.dirname(outFile), { recursive: true });
fs.writeFileSync(outFile, JSON.stringify(manifest));
console.log(`Wrote ${files.length} UVM manifest entries to ${outFile}`);
NODE

# Remove legacy mock shim artifacts so the runtime cannot silently pick stale
# files from earlier experiments.
rm -f "$DST_DIR/mox.js" "$DST_DIR/mox.wasm"
rm -f "$DST_DIR/uvm-core/uvm-source-map.json"

# Browser compatibility shim for mox-sim builds linked with NODERAWFS.
# Upstream sim wasm artifacts may include Node-only glue even when consumed
# from a web worker. Patch those sections to keep the tutorial runtime web-safe.
node - "$DST_DIR/mox-sim.js" <<'NODE'
const fs = require('fs');

const simPath = process.argv[2];
let source = fs.readFileSync(simPath, 'utf8');

const browserPathDef =
  'var PATH={isAbs:path=>path.charAt(0)==="/",splitPath:filename=>{var splitPathRe=/^(\\/?|)([\\s\\S]*?)((?:\\.{1,2}|[^\\/]+?|)(\\.[^.\\/]*|))(?:[\\/]*)$/;return splitPathRe.exec(filename).slice(1)},normalizeArray:(parts,allowAboveRoot)=>{var up=0;for(var i=parts.length-1;i>=0;i--){var last=parts[i];if(last==="."){parts.splice(i,1)}else if(last===".."){parts.splice(i,1);up++}else if(up){parts.splice(i,1);up--}}if(allowAboveRoot){for(;up;up--){parts.unshift("..")}}return parts},normalize:path=>{var isAbsolute=PATH.isAbs(path),trailingSlash=path.slice(-1)==="/";path=PATH.normalizeArray(path.split("/").filter(p=>!!p),!isAbsolute).join("/");if(!path&&!isAbsolute){path="."}if(path&&trailingSlash){path+="/"}return(isAbsolute?"/":"")+path},dirname:path=>{var result=PATH.splitPath(path),root=result[0],dir=result[1];if(!root&&!dir){return"."}if(dir){dir=dir.slice(0,-1)}return root+dir},basename:path=>path&&path.match(/([^\\/]+|\\/)\\/*$/)[1],join:(...paths)=>PATH.normalize(paths.join("/")),join2:(l,r)=>PATH.normalize(l+"/"+r)};';
const browserPathFsDef =
  'var PATH_FS={resolve:(...args)=>{var resolvedPath="",resolvedAbsolute=false;for(var i=args.length-1;i>=-1&&!resolvedAbsolute;i--){var path=i>=0?args[i]:FS.cwd();if(typeof path!="string"){throw new TypeError("Arguments to path.resolve must be strings")}else if(!path){return""}resolvedPath=path+"/"+resolvedPath;resolvedAbsolute=PATH.isAbs(path)}resolvedPath=PATH.normalizeArray(resolvedPath.split("/").filter(p=>!!p),!resolvedAbsolute).join("/");return(resolvedAbsolute?"/":"")+resolvedPath||"."},relative:(from,to)=>{from=PATH_FS.resolve(from).slice(1);to=PATH_FS.resolve(to).slice(1);function trim(arr){var start=0;for(;start<arr.length;start++){if(arr[start]!=="")break}var end=arr.length-1;for(;end>=0;end--){if(arr[end]!=="")break}if(start>end)return[];return arr.slice(start,end-start+1)}var fromParts=trim(from.split("/"));var toParts=trim(to.split("/"));var length=Math.min(fromParts.length,toParts.length);var samePartsLength=length;for(var i=0;i<length;i++){if(fromParts[i]!==toParts[i]){samePartsLength=i;break}}var outputParts=[];for(var i=samePartsLength;i<fromParts.length;i++){outputParts.push("..")}outputParts=outputParts.concat(toParts.slice(samePartsLength));return outputParts.join("/")}};';

const replaceExact = (regex, replacement, label) => {
  if (regex.test(source)) {
    source = source.replace(regex, replacement);
    return;
  }
  if (source.includes(replacement)) {
    console.log(`Skipped patch (${label}): already applied`);
    return;
  }
  throw new Error(`failed to patch mox-sim.js (${label})`);
};

replaceExact(
  /var nodePath=require\("path"\);var PATH=\{isAbs:nodePath\.isAbsolute,normalize:nodePath\.normalize,dirname:nodePath\.dirname,basename:nodePath\.basename,join:nodePath\.join,join2:nodePath\.join\};/,
  browserPathDef,
  'path definition'
);

replaceExact(
  /var PATH_FS=\{resolve:\(\.\.\.paths\)=>\{paths\.unshift\(FS\.cwd\(\)\);return nodePath\.posix\.resolve\(\.\.\.paths\)\},relative:\(from,to\)=>nodePath\.posix\.relative\(from\|\|FS\.cwd\(\),to\|\|FS\.cwd\(\)\)\};/,
  browserPathFsDef,
  'PATH_FS definition'
);

replaceExact(
  /if\(ENVIRONMENT_IS_NODE\)\{NODEFS\.staticInit\(\)\}if\(!ENVIRONMENT_IS_NODE\)\{throw new Error\("NODERAWFS is currently only supported on Node\.js environment\."\)\}var _wrapNodeError=function\(func\)\{return function\(\.\.\.args\)\{try\{return func\(\.\.\.args\)\}catch\(e\)\{if\(e\.code\)\{throw new FS\.ErrnoError\(ERRNO_CODES\[e\.code\]\)\}throw e\}\}\};var VFS=\{\.\.\.FS\};for\(var _key in NODERAWFS\)\{FS\[_key\]=_wrapNodeError\(NODERAWFS\[_key\]\)\}/,
  'var VFS={...FS};',
  'NODERAWFS bootstrap'
);

fs.writeFileSync(simPath, source);
console.log(`Patched browser compatibility in ${simPath}`);
NODE

# Apply the same browser compatibility patch to mox-sim-vpi.js if present.
if [ "$HAVE_VPI" -eq 1 ]; then
node - "$DST_DIR/mox-sim-vpi.js" <<'NODE'
const fs = require('fs');

const simPath = process.argv[2];
let source = fs.readFileSync(simPath, 'utf8');

const browserPathDef =
  'var PATH={isAbs:path=>path.charAt(0)==="/",splitPath:filename=>{var splitPathRe=/^(\\/?|)([\\s\\S]*?)((?:\\.{1,2}|[^\\/]+?|)(\\.[^.\\/]*|))(?:[\\/]*)$/;return splitPathRe.exec(filename).slice(1)},normalizeArray:(parts,allowAboveRoot)=>{var up=0;for(var i=parts.length-1;i>=0;i--){var last=parts[i];if(last==="."){parts.splice(i,1)}else if(last===".."){parts.splice(i,1);up++}else if(up){parts.splice(i,1);up--}}if(allowAboveRoot){for(;up;up--){parts.unshift("..")}}return parts},normalize:path=>{var isAbsolute=PATH.isAbs(path),trailingSlash=path.slice(-1)==="/";path=PATH.normalizeArray(path.split("/").filter(p=>!!p),!isAbsolute).join("/");if(!path&&!isAbsolute){path="."}if(path&&trailingSlash){path+="/"}return(isAbsolute?"/":"")+path},dirname:path=>{var result=PATH.splitPath(path),root=result[0],dir=result[1];if(!root&&!dir){return"."}if(dir){dir=dir.slice(0,-1)}return root+dir},basename:path=>path&&path.match(/([^\\/]+|\\/)\\/*$/)[1],join:(...paths)=>PATH.normalize(paths.join("/")),join2:(l,r)=>PATH.normalize(l+"/"+r)};';
const browserPathFsDef =
  'var PATH_FS={resolve:(...args)=>{var resolvedPath="",resolvedAbsolute=false;for(var i=args.length-1;i>=-1&&!resolvedAbsolute;i--){var path=i>=0?args[i]:FS.cwd();if(typeof path!="string"){throw new TypeError("Arguments to path.resolve must be strings")}else if(!path){return""}resolvedPath=path+"/"+resolvedPath;resolvedAbsolute=PATH.isAbs(path)}resolvedPath=PATH.normalizeArray(resolvedPath.split("/").filter(p=>!!p),!resolvedAbsolute).join("/");return(resolvedAbsolute?"/":"")+resolvedPath||"."},relative:(from,to)=>{from=PATH_FS.resolve(from).slice(1);to=PATH_FS.resolve(to).slice(1);function trim(arr){var start=0;for(;start<arr.length;start++){if(arr[start]!=="")break}var end=arr.length-1;for(;end>=0;end--){if(arr[end]!=="")break}if(start>end)return[];return arr.slice(start,end-start+1)}var fromParts=trim(from.split("/"));var toParts=trim(to.split("/"));var length=Math.min(fromParts.length,toParts.length);var samePartsLength=length;for(var i=0;i<length;i++){if(fromParts[i]!==toParts[i]){samePartsLength=i;break}}var outputParts=[];for(var i=samePartsLength;i<fromParts.length;i++){outputParts.push("..")}outputParts=outputParts.concat(toParts.slice(samePartsLength));return outputParts.join("/")}};';

const replaceExact = (regex, replacement, label) => {
  if (regex.test(source)) {
    source = source.replace(regex, replacement);
    return;
  }
  if (source.includes(replacement)) {
    console.log(`Skipped patch (${label}): already applied`);
    return;
  }
  throw new Error(`failed to patch mox-sim-vpi.js (${label})`);
};

replaceExact(
  /var nodePath=require\("path"\);var PATH=\{isAbs:nodePath\.isAbsolute,normalize:nodePath\.normalize,dirname:nodePath\.dirname,basename:nodePath\.basename,join:nodePath\.join,join2:nodePath\.join\};/,
  browserPathDef,
  'path definition'
);

replaceExact(
  /var PATH_FS=\{resolve:\(\.\.\.paths\)=>\{paths\.unshift\(FS\.cwd\(\)\);return nodePath\.posix\.resolve\(\.\.\.paths\)\},relative:\(from,to\)=>nodePath\.posix\.relative\(from\|\|FS\.cwd\(\),to\|\|FS\.cwd\(\)\)\};/,
  browserPathFsDef,
  'PATH_FS definition'
);

replaceExact(
  /if\(ENVIRONMENT_IS_NODE\)\{NODEFS\.staticInit\(\)\}if\(!ENVIRONMENT_IS_NODE\)\{throw new Error\("NODERAWFS is currently only supported on Node\.js environment\."\)\}var _wrapNodeError=function\(func\)\{return function\(\.\.\.args\)\{try\{return func\(\.\.\.args\)\}catch\(e\)\{if\(e\.code\)\{throw new FS\.ErrnoError\(ERRNO_CODES\[e\.code\]\)\}throw e\}\}\};var VFS=\{\.\.\.FS\};for\(var _key in NODERAWFS\)\{FS\[_key\]=_wrapNodeError\(NODERAWFS\[_key\]\)\}/,
  'var VFS={...FS};',
  'NODERAWFS bootstrap'
);

// Wrap the VPI yield table call in try-catch so any cbFuncPtr value is safe.
// VPIRuntime::registerCb requires non-null cb_rtn; we pass a placeholder (1).
// The JS yield hook handles all dispatch; the table call is a formality.
replaceExact(
  /if\(cbFuncPtr\)return (?:await )?wasmTable\.get\(cbFuncPtr\)\(cbDataPtr\);return 0/,
  'if(cbFuncPtr){try{return wasmTable.get(cbFuncPtr)(cbDataPtr);}catch(e){}}return 0',
  'vpi yield try-catch'
);

// Fix instrumentWasmImports: the Emscripten stub detects async imports but
// never wraps them.  Without this patch, _mox_vpi_wasm_yield is called as
// a plain async function from WASM, returns a Promise that gets coerced to 0,
// and Asyncify never triggers (simulation runs synchronously with no VPI).
replaceExact(
  /let isAsyncifyImport=original\.isAsync\|\|importPattern\.test\(x\)/,
  'let isAsyncifyImport=original.isAsync||importPattern.test(x);if(isAsyncifyImport){imports[x]=(...args)=>Asyncify.handleAsync(()=>original(...args))}',
  'instrumentWasmImports async wrapping'
);

fs.writeFileSync(simPath, source);
console.log(`Patched browser compatibility in ${simPath}`);
NODE
fi

cat >"$DST_DIR/package.json" <<'EOF'
{
  "type": "commonjs"
}
EOF

echo "Synced MOX wasm artifacts:"
for tool in "${TOOLS[@]}"; do
  ls -lh "$DST_DIR/$tool.js" "$DST_DIR/$tool.wasm"
done
if [ "$HAVE_VPI" -eq 1 ]; then
  echo "Synced VPI-capable sim:"
  ls -lh "$DST_DIR/$VPI_TOOL.js" "$DST_DIR/$VPI_TOOL.wasm"
fi
echo "Synced full UVM source files:"
echo "  source dir: $UVM_DST_DIR"
echo "  manifest: $UVM_MANIFEST_PATH"

# --publish: upload artifacts to the mox-wasm GitHub release and update the
# toolchain lock so CI rebuilds from the same commit.
if [ "$PUBLISH" -eq 1 ]; then
  ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
  source "$ROOT_DIR/scripts/toolchain.lock.sh"

  MOX_COMMIT="$(git -C "${MOX_DIR:-vendor/mox}" rev-parse HEAD 2>/dev/null || true)"
  if [ -z "$MOX_COMMIT" ]; then
    echo "--publish: could not determine MOX commit from ${MOX_DIR:-vendor/mox}" >&2
    exit 1
  fi

  # Bundle UVM sources for the release asset. The release asset name is the
  # file's basename, and the deploy workflow looks for `uvm-core.tar.gz`, so the
  # bundle must be named exactly that. Build it inside a mktemp -d directory for
  # uniqueness instead of embedding Xs in the filename (mktemp only substitutes
  # *trailing* Xs, so `uvm-core.XXXXXX.tar.gz` yields a literal-`XXXXXX` name).
  UVM_BUNDLE_DIR="$(mktemp -d)"
  UVM_BUNDLE="$UVM_BUNDLE_DIR/uvm-core.tar.gz"
  tar -czf "$UVM_BUNDLE" -C "$DST_DIR" uvm-core
  echo "Created UVM bundle: $UVM_BUNDLE"

  # Upload all artifacts, replacing existing assets on the release.
  RELEASE_ASSETS=(
    "$DST_DIR/mox-bmc.js"   "$DST_DIR/mox-bmc.wasm"
    "$DST_DIR/mox-sim.js"   "$DST_DIR/mox-sim.wasm"
    "$DST_DIR/mox-verilog.js" "$DST_DIR/mox-verilog.wasm"
    "$DST_DIR/mox-lec.js"   "$DST_DIR/mox-lec.wasm"
    "$UVM_BUNDLE"
  )
  if [ "$HAVE_VPI" -eq 1 ]; then
    RELEASE_ASSETS+=("$DST_DIR/$VPI_TOOL.js" "$DST_DIR/$VPI_TOOL.wasm")
  fi

  echo "Uploading to GitHub release 'mox-wasm'..."
  gh release upload mox-wasm "${RELEASE_ASSETS[@]}" --clobber
  rm -rf "$UVM_BUNDLE_DIR"
  echo "GitHub release updated."

  # Update toolchain lock to the current MOX commit.
  LOCK_FILE="$ROOT_DIR/scripts/toolchain.lock.sh"
  sed -i.bak "s|^readonly MOX_REF_LOCKED=.*|readonly MOX_REF_LOCKED=\"$MOX_COMMIT\"|" "$LOCK_FILE"
  rm -f "$LOCK_FILE.bak"
  echo "Updated MOX_REF_LOCKED to $MOX_COMMIT in $LOCK_FILE"
fi
