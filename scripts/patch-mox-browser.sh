#!/usr/bin/env bash
# Apply the browser-compatibility patches to MOX wasm tool artifacts in <dir>.
#
# The upstream wasm tools are linked with NODERAWFS and embed Node-only path/fs
# glue plus a Node-only `callMain` that the in-browser worker can't reach. These
# patches:
#   1. expose `callMain` as `self.__svt_callMain` (all tools),
#   2. rewrite the NODERAWFS path/fs bootstrap to a browser/MEMFS-safe form
#      (mox-sim, mox-verilog, mox-bmc — mox-lec is a MEMFS build and is skipped),
#   3. additionally fix VPI Asyncify wrapping for mox-sim-vpi.
#
# All patches are idempotent (already-applied → skipped), so this is safe to run
# at publish time (scripts/sync-mox-wasm.sh) AND at deploy time on artifacts
# downloaded from the release (.github/workflows/deploy.yml). Keeping it as one
# script means the patch logic has a single source of truth.
#
# Usage: scripts/patch-mox-browser.sh <dir>
set -euo pipefail

DIR="${1:?usage: patch-mox-browser.sh <dir-containing-mox-*.js>}"

# 1. callMain shim — every tool .js that exists in DIR.
for tool in mox-verilog mox-sim mox-bmc mox-lec mox-sim-vpi; do
  js="$DIR/$tool.js"
  [ -f "$js" ] || continue
  node - "$js" <<'NODE'
const fs = require('fs');
const jsPath = process.argv[2];
let source = fs.readFileSync(jsPath, 'utf8');
if (source.includes('__svt_callMain')) {
  console.log(`Skipped callMain shim (already present): ${jsPath}`);
  process.exit(0);
}
if (!source.includes('function callMain(')) {
  console.log(`Skipped callMain shim (no callMain symbol): ${jsPath}`);
  process.exit(0);
}
source += '\n;try{if(typeof callMain==="function"&&typeof self!=="undefined"&&typeof self.__svt_callMain!=="function"){self.__svt_callMain=callMain;}}catch(_){}\n';
fs.writeFileSync(jsPath, source);
console.log(`Patched callMain shim in ${jsPath}`);
NODE
done

# 2. NODERAWFS -> browser/MEMFS path/fs rewrite for the NODERAWFS tools.
node - "$DIR/mox-sim.js" "$DIR/mox-verilog.js" "$DIR/mox-bmc.js" <<'NODE'
const fs = require('fs');
const targetPaths = process.argv.slice(2);

const browserPathDef =
  'var PATH={isAbs:path=>path.charAt(0)==="/",splitPath:filename=>{var splitPathRe=/^(\\/?|)([\\s\\S]*?)((?:\\.{1,2}|[^\\/]+?|)(\\.[^.\\/]*|))(?:[\\/]*)$/;return splitPathRe.exec(filename).slice(1)},normalizeArray:(parts,allowAboveRoot)=>{var up=0;for(var i=parts.length-1;i>=0;i--){var last=parts[i];if(last==="."){parts.splice(i,1)}else if(last===".."){parts.splice(i,1);up++}else if(up){parts.splice(i,1);up--}}if(allowAboveRoot){for(;up;up--){parts.unshift("..")}}return parts},normalize:path=>{var isAbsolute=PATH.isAbs(path),trailingSlash=path.slice(-1)==="/";path=PATH.normalizeArray(path.split("/").filter(p=>!!p),!isAbsolute).join("/");if(!path&&!isAbsolute){path="."}if(path&&trailingSlash){path+="/"}return(isAbsolute?"/":"")+path},dirname:path=>{var result=PATH.splitPath(path),root=result[0],dir=result[1];if(!root&&!dir){return"."}if(dir){dir=dir.slice(0,-1)}return root+dir},basename:path=>path&&path.match(/([^\\/]+|\\/)\\/*$/)[1],join:(...paths)=>PATH.normalize(paths.join("/")),join2:(l,r)=>PATH.normalize(l+"/"+r)};';
const browserPathFsDef =
  'var PATH_FS={resolve:(...args)=>{var resolvedPath="",resolvedAbsolute=false;for(var i=args.length-1;i>=-1&&!resolvedAbsolute;i--){var path=i>=0?args[i]:FS.cwd();if(typeof path!="string"){throw new TypeError("Arguments to path.resolve must be strings")}else if(!path){return""}resolvedPath=path+"/"+resolvedPath;resolvedAbsolute=PATH.isAbs(path)}resolvedPath=PATH.normalizeArray(resolvedPath.split("/").filter(p=>!!p),!resolvedAbsolute).join("/");return(resolvedAbsolute?"/":"")+resolvedPath||"."},relative:(from,to)=>{from=PATH_FS.resolve(from).slice(1);to=PATH_FS.resolve(to).slice(1);function trim(arr){var start=0;for(;start<arr.length;start++){if(arr[start]!=="")break}var end=arr.length-1;for(;end>=0;end--){if(arr[end]!=="")break}if(start>end)return[];return arr.slice(start,end-start+1)}var fromParts=trim(from.split("/"));var toParts=trim(to.split("/"));var length=Math.min(fromParts.length,toParts.length);var samePartsLength=length;for(var i=0;i<length;i++){if(fromParts[i]!==toParts[i]){samePartsLength=i;break}}var outputParts=[];for(var i=samePartsLength;i<fromParts.length;i++){outputParts.push("..")}outputParts=outputParts.concat(toParts.slice(samePartsLength));return outputParts.join("/")}};';

function patchFile(simPath) {
  if (!fs.existsSync(simPath)) { console.log(`Skipped (missing): ${simPath}`); return; }
  let source = fs.readFileSync(simPath, 'utf8');
  const replaceExact = (regex, replacement, label) => {
    if (regex.test(source)) { source = source.replace(regex, replacement); return; }
    if (source.includes(replacement)) { console.log(`Skipped patch (${label}): already applied in ${simPath}`); return; }
    throw new Error(`failed to patch ${simPath} (${label})`);
  };
  replaceExact(
    /var nodePath=require\("path"\);var PATH=\{isAbs:nodePath\.isAbsolute,normalize:nodePath\.normalize,dirname:nodePath\.dirname,basename:nodePath\.basename,join:nodePath\.join,join2:nodePath\.join\};/,
    browserPathDef, 'path definition');
  replaceExact(
    /var PATH_FS=\{resolve:\(\.\.\.paths\)=>\{paths\.unshift\(FS\.cwd\(\)\);return nodePath\.posix\.resolve\(\.\.\.paths\)\},relative:\(from,to\)=>nodePath\.posix\.relative\(from\|\|FS\.cwd\(\),to\|\|FS\.cwd\(\)\)\};/,
    browserPathFsDef, 'PATH_FS definition');
  replaceExact(
    /if\(ENVIRONMENT_IS_NODE\)\{NODEFS\.staticInit\(\)\}if\(!ENVIRONMENT_IS_NODE\)\{throw new Error\("NODERAWFS is currently only supported on Node\.js environment\."\)\}var _wrapNodeError=function\(func\)\{return function\(\.\.\.args\)\{try\{return func\(\.\.\.args\)\}catch\(e\)\{if\(e\.code\)\{throw new FS\.ErrnoError\(ERRNO_CODES\[e\.code\]\)\}throw e\}\}\};var VFS=\{\.\.\.FS\};for\(var _key in NODERAWFS\)\{FS\[_key\]=_wrapNodeError\(NODERAWFS\[_key\]\)\}/,
    'var VFS={...FS};', 'NODERAWFS bootstrap');
  fs.writeFileSync(simPath, source);
  console.log(`Patched browser compatibility in ${simPath}`);
}
for (const p of targetPaths) patchFile(p);
NODE

# 3. mox-sim-vpi: browser path/fs rewrite + VPI Asyncify fixes.
if [ -f "$DIR/mox-sim-vpi.js" ]; then
node - "$DIR/mox-sim-vpi.js" <<'NODE'
const fs = require('fs');
const simPath = process.argv[2];
let source = fs.readFileSync(simPath, 'utf8');

const browserPathDef =
  'var PATH={isAbs:path=>path.charAt(0)==="/",splitPath:filename=>{var splitPathRe=/^(\\/?|)([\\s\\S]*?)((?:\\.{1,2}|[^\\/]+?|)(\\.[^.\\/]*|))(?:[\\/]*)$/;return splitPathRe.exec(filename).slice(1)},normalizeArray:(parts,allowAboveRoot)=>{var up=0;for(var i=parts.length-1;i>=0;i--){var last=parts[i];if(last==="."){parts.splice(i,1)}else if(last===".."){parts.splice(i,1);up++}else if(up){parts.splice(i,1);up--}}if(allowAboveRoot){for(;up;up--){parts.unshift("..")}}return parts},normalize:path=>{var isAbsolute=PATH.isAbs(path),trailingSlash=path.slice(-1)==="/";path=PATH.normalizeArray(path.split("/").filter(p=>!!p),!isAbsolute).join("/");if(!path&&!isAbsolute){path="."}if(path&&trailingSlash){path+="/"}return(isAbsolute?"/":"")+path},dirname:path=>{var result=PATH.splitPath(path),root=result[0],dir=result[1];if(!root&&!dir){return"."}if(dir){dir=dir.slice(0,-1)}return root+dir},basename:path=>path&&path.match(/([^\\/]+|\\/)\\/*$/)[1],join:(...paths)=>PATH.normalize(paths.join("/")),join2:(l,r)=>PATH.normalize(l+"/"+r)};';
const browserPathFsDef =
  'var PATH_FS={resolve:(...args)=>{var resolvedPath="",resolvedAbsolute=false;for(var i=args.length-1;i>=-1&&!resolvedAbsolute;i--){var path=i>=0?args[i]:FS.cwd();if(typeof path!="string"){throw new TypeError("Arguments to path.resolve must be strings")}else if(!path){return""}resolvedPath=path+"/"+resolvedPath;resolvedAbsolute=PATH.isAbs(path)}resolvedPath=PATH.normalizeArray(resolvedPath.split("/").filter(p=>!!p),!resolvedAbsolute).join("/");return(resolvedAbsolute?"/":"")+resolvedPath||"."},relative:(from,to)=>{from=PATH_FS.resolve(from).slice(1);to=PATH_FS.resolve(to).slice(1);function trim(arr){var start=0;for(;start<arr.length;start++){if(arr[start]!=="")break}var end=arr.length-1;for(;end>=0;end--){if(arr[end]!=="")break}if(start>end)return[];return arr.slice(start,end-start+1)}var fromParts=trim(from.split("/"));var toParts=trim(to.split("/"));var length=Math.min(fromParts.length,toParts.length);var samePartsLength=length;for(var i=0;i<length;i++){if(fromParts[i]!==toParts[i]){samePartsLength=i;break}}var outputParts=[];for(var i=samePartsLength;i<fromParts.length;i++){outputParts.push("..")}outputParts=outputParts.concat(toParts.slice(samePartsLength));return outputParts.join("/")}};';

const replaceExact = (regex, replacement, label) => {
  if (regex.test(source)) { source = source.replace(regex, replacement); return; }
  if (source.includes(replacement)) { console.log(`Skipped patch (${label}): already applied`); return; }
  throw new Error(`failed to patch mox-sim-vpi.js (${label})`);
};
replaceExact(
  /var nodePath=require\("path"\);var PATH=\{isAbs:nodePath\.isAbsolute,normalize:nodePath\.normalize,dirname:nodePath\.dirname,basename:nodePath\.basename,join:nodePath\.join,join2:nodePath\.join\};/,
  browserPathDef, 'path definition');
replaceExact(
  /var PATH_FS=\{resolve:\(\.\.\.paths\)=>\{paths\.unshift\(FS\.cwd\(\)\);return nodePath\.posix\.resolve\(\.\.\.paths\)\},relative:\(from,to\)=>nodePath\.posix\.relative\(from\|\|FS\.cwd\(\),to\|\|FS\.cwd\(\)\)\};/,
  browserPathFsDef, 'PATH_FS definition');
replaceExact(
  /if\(ENVIRONMENT_IS_NODE\)\{NODEFS\.staticInit\(\)\}if\(!ENVIRONMENT_IS_NODE\)\{throw new Error\("NODERAWFS is currently only supported on Node\.js environment\."\)\}var _wrapNodeError=function\(func\)\{return function\(\.\.\.args\)\{try\{return func\(\.\.\.args\)\}catch\(e\)\{if\(e\.code\)\{throw new FS\.ErrnoError\(ERRNO_CODES\[e\.code\]\)\}throw e\}\}\};var VFS=\{\.\.\.FS\};for\(var _key in NODERAWFS\)\{FS\[_key\]=_wrapNodeError\(NODERAWFS\[_key\]\)\}/,
  'var VFS={...FS};', 'NODERAWFS bootstrap');
replaceExact(
  /if\(cbFuncPtr\)return (?:await )?wasmTable\.get\(cbFuncPtr\)\(cbDataPtr\);return 0/,
  'if(cbFuncPtr){try{return wasmTable.get(cbFuncPtr)(cbDataPtr);}catch(e){}}return 0',
  'vpi yield try-catch');
replaceExact(
  /let isAsyncifyImport=original\.isAsync\|\|importPattern\.test\(x\)/,
  'let isAsyncifyImport=original.isAsync||importPattern.test(x);if(isAsyncifyImport){imports[x]=(...args)=>Asyncify.handleAsync(()=>original(...args))}',
  'instrumentWasmImports async wrapping');
fs.writeFileSync(simPath, source);
console.log(`Patched browser compatibility in ${simPath}`);
NODE
fi

echo "[patch-mox-browser] done: $DIR"
