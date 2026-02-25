export const WORKER_NODE_COMPAT_SOURCE = String.raw`
function setupWorkerNodeCompat(opts) {
  var options = opts || {};
  var pathShim = options.pathShim || null;
  var fsApi = options.fsApi || null;
  var onStdout = (typeof options.onStdout === 'function') ? options.onStdout : function() {};
  var onStderr = (typeof options.onStderr === 'function') ? options.onStderr : function() {};

  if (typeof self.__dirname === 'undefined') self.__dirname = '/';
  if (typeof self.__filename === 'undefined') self.__filename = '/tool.js';

  var proc = (typeof self.process === 'undefined' || self.process === null) ? {} : self.process;
  if (!proc.versions || typeof proc.versions !== 'object') proc.versions = {};
  if (!proc.versions.node) proc.versions.node = '18.0.0';
  if (typeof proc.version !== 'string') proc.version = 'v18.0.0';
  if (typeof proc.platform !== 'string') proc.platform = 'linux';
  if (!Array.isArray(proc.argv)) proc.argv = ['node', '/tool'];
  if (!proc.type) proc.type = 'worker';
  if (typeof proc.exitCode !== 'number') proc.exitCode = 0;

  // Emscripten calls process.exit(code) in Node.js mode.
  if (typeof proc.exit !== 'function') {
    proc.exit = function(code) {
      throw { name: 'ExitStatus', message: 'exit(' + (code | 0) + ')', status: (code | 0) };
    };
  }
  if (typeof proc.on !== 'function') proc.on = function() { return proc; };
  if (!proc.stdout || typeof proc.stdout !== 'object') proc.stdout = {};
  if (!proc.stderr || typeof proc.stderr !== 'object') proc.stderr = {};
  proc.stdout.write = function(s) { onStdout(String(s)); };
  proc.stdout.isTTY = false;
  proc.stderr.write = function(s) { onStderr(String(s)); };
  proc.stderr.isTTY = false;
  proc.stdin = proc.stdin || null;
  if (!proc.env || typeof proc.env !== 'object') proc.env = {};
  if (typeof proc.cwd !== 'function') proc.cwd = function() { return '/workspace'; };
  proc.binding = function(name) {
    if (name === 'constants') {
      return {
        fs: {
          O_APPEND: 1024,
          O_CREAT: 64,
          O_EXCL: 128,
          O_NOCTTY: 256,
          O_RDONLY: 0,
          O_RDWR: 2,
          O_SYNC: 4096,
          O_TRUNC: 512,
          O_WRONLY: 1,
          O_NOFOLLOW: 131072
        }
      };
    }
    throw new Error('process.binding(' + String(name) + ') is not available');
  };

  self.process = proc;
  if (typeof self.global === 'undefined') self.global = self;
  self.require = function(mod) {
    if ((mod === 'path' || mod === 'node:path') && pathShim) return pathShim;
    if ((mod === 'fs' || mod === 'node:fs') && fsApi) return fsApi;
    if (mod === 'crypto' || mod === 'node:crypto') {
      return { randomBytes: function(n) { return crypto.getRandomValues(new Uint8Array(n)); } };
    }
    if (mod === 'child_process' || mod === 'node:child_process') {
      return { spawnSync: function() { return { status: 1, stdout: '', stderr: '' }; } };
    }
    throw new Error('require(\'' + mod + '\') is not available in browser worker');
  };
}
`;
