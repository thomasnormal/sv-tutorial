import { WORKER_NODE_COMPAT_SOURCE } from './worker-node-compat-source.js';

export const WORKER_RUNTIME_HELPERS_SOURCE = String.raw`
${WORKER_NODE_COMPAT_SOURCE}

// Minimal POSIX path shim — used as the return value of require('path') for
// Emscripten builds that call require('path') unconditionally at module level.
var WORKER_PATH_SHIM = {
  sep: '/',
  isAbsolute: function(p) { return String(p).charAt(0) === '/'; },
  normalize: function(p) { return String(p).replace(/\/+/g, '/').replace(/(.)\/$/, '$1') || '/'; },
  dirname: function(p) { var s = String(p); var i = s.lastIndexOf('/'); return i <= 0 ? '/' : s.slice(0, i); },
  basename: function(p, ext) { var b = String(p).split('/').pop() || ''; return ext && b.slice(-ext.length) === ext ? b.slice(0, -ext.length) : b; },
  extname: function(p) { var b = String(p).split('/').pop() || ''; var i = b.lastIndexOf('.'); return i <= 0 ? '' : b.slice(i); },
  join: function() { return Array.prototype.slice.call(arguments).join('/').replace(/\/+/g, '/'); },
  join2: function(a, b) { return (String(a) + '/' + String(b)).replace(/\/+/g, '/'); },
  resolve: function() { return Array.prototype.slice.call(arguments).join('/').replace(/\/+/g, '/'); }
};
WORKER_PATH_SHIM.posix = WORKER_PATH_SHIM;

function isNoderawfsScript(scriptText) {
  var text = String(scriptText || '');
  return (
    text.indexOf('NODERAWFS is currently only supported') >= 0 ||
    text.indexOf('var nodePath=require(') >= 0
  );
}

async function fetchScriptText(url) {
  try {
    var response = await fetch(url);
    if (!response.ok) return null;
    return await response.text();
  } catch(_) {
    return null;
  }
}

function installPathRequireOnly(pathShim) {
  if (typeof self.require !== 'undefined') return;
  self.require = function(mod) {
    if (mod === 'path') return pathShim;
    throw new Error('require(\'' + mod + '\') is not available in browser worker');
  };
}

async function loadEmscriptenTool(opts) {
  var options = opts || {};
  var jsUrl = options.jsUrl;
  var pathShim = options.pathShim || WORKER_PATH_SHIM;
  var makeFs = (typeof options.makeFs === 'function') ? options.makeFs : null;
  var onStdout = (typeof options.onStdout === 'function') ? options.onStdout : function() {};
  var onStderr = (typeof options.onStderr === 'function') ? options.onStderr : function() {};
  var onMode = (typeof options.onMode === 'function') ? options.onMode : null;
  var beforeEval = (typeof options.beforeEval === 'function') ? options.beforeEval : null;
  var afterEval = (typeof options.afterEval === 'function') ? options.afterEval : null;

  var scriptText = await fetchScriptText(jsUrl);
  var isNoderawfs = !!scriptText && isNoderawfsScript(scriptText);
  var fsBundle = null;

  if (isNoderawfs) {
    if (onMode) onMode('noderawfs');
    if (makeFs) fsBundle = makeFs();
    setupWorkerNodeCompat({
      pathShim: pathShim,
      fsApi: fsBundle && fsBundle.nodeApi ? fsBundle.nodeApi : null,
      onStdout: onStdout,
      onStderr: onStderr
    });
    if (beforeEval) beforeEval();
    (0, eval)(scriptText);
    if (afterEval) afterEval();
  } else {
    if (onMode) onMode('browser');
    installPathRequireOnly(pathShim);
    importScripts(jsUrl);
  }

  return {
    scriptText: scriptText,
    isNoderawfs: isNoderawfs,
    fs: fsBundle
  };
}
`;
