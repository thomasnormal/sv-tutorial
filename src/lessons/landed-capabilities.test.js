import { describe, expect, it } from 'vitest';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import path from 'node:path';
import meta from './meta.js';

const root = path.resolve(process.cwd(), 'src/lessons');
const capabilities = [
  ['sv/macro-formal-continuation', 'macro_formal'],
  ['sv/struct-field-refs', 'struct_field'],
  ['sv/indexed-part-select', 'indexed_part_select'],
  ['sv/nested-child-input', 'nested_child_input'],
  ['sv/sequential-udp-init', 'sequential_udp']
];

describe('landed Mox capability lessons and status pages', () => {
  it('are registered with runnable simulation metadata', () => {
    for (const [slug, basename] of capabilities) {
      expect(meta[slug]?.runner ?? 'sim').toBe('sim');
      const dir = path.join(root, slug);
      const source = readFileSync(path.join(dir, `${basename}.sv`), 'utf8');
      const solution = readFileSync(path.join(dir, `${basename}.sol.sv`), 'utf8');
      expect(source).toContain('module tb');
      expect(solution).toContain('$display("PASS")');
    }
  });

  it('keeps the indexed-select starter unsolved and its range wording precise', () => {
    const dir = path.join(root, 'sv/indexed-part-select');
    const source = readFileSync(path.join(dir, 'indexed_part_select.sv'), 'utf8');
    const description = readFileSync(path.join(dir, 'description.html'), 'utf8');
    const receipts = readFileSync(
      path.resolve(process.cwd(), 'artifacts/tutorial/capability-receipts/final-summary.tsv'),
      'utf8'
    );
    expect(source).toContain('base = 2;');
    expect(source).toContain("inside_slice !== 4'b1101");
    expect(description).toContain('completely out-of-range read');
    expect(description).not.toContain('A partially out-of-range read returns');
    expect(receipts).toContain('sv/indexed-part-select\tstarter\tinterpret\t0\tFAIL: inside=0101 partial=xxxx');
    expect(receipts).toContain('sv/indexed-part-select\tstarter\tcompile\t0\tFAIL: inside=0101 partial=xxxx');
  });

  it('calibrates the sequential UDP initializer exercise', () => {
    const dir = path.join(root, 'sv/sequential-udp-init');
    const starter = readFileSync(path.join(dir, 'sequential_udp.sv'), 'utf8');
    const solution = readFileSync(path.join(dir, 'sequential_udp.sol.sv'), 'utf8');
    const description = readFileSync(path.join(dir, 'description.html'), 'utf8');
    const receipts = readFileSync(
      path.resolve(process.cwd(), 'artifacts/tutorial/capability-receipts/final-summary.tsv'),
      'utf8'
    );
    expect(starter).toContain("output reg q = 1'b0");
    expect(solution).toContain("output reg q = 1'b1");
    expect(description).toContain('§29.3.2');
    expect(description).toContain('§29.7');
    expect(receipts).toContain('sv/sequential-udp-init\tstarter\tinterpret\t0\tFAIL: initial q=0');
    expect(receipts).toContain('sv/sequential-udp-init\tsolution\trefdiff\t0\t');
  });

  it('binds sequential UDP refdiff receipts to committed source blobs', () => {
    const dir = path.join(root, 'sv/sequential-udp-init');
    for (const [variant, filename] of [
      ['starter', 'sequential_udp.sv'],
      ['solution', 'sequential_udp.sol.sv']
    ]) {
      const sourcePath = path.join(dir, filename);
      const sourceHash = createHash('sha256')
        .update(readFileSync(sourcePath))
        .digest('hex');
      const receipt = JSON.parse(readFileSync(
        path.resolve(
          process.cwd(),
          `artifacts/tutorial/capability-receipts/sv__sequential-udp-init__${variant}__refdiff.final.txt`
        ),
        'utf8'
      ));
      expect(receipt.source).toBe(sourcePath);
      expect(receipt.sha256).toBe(sourceHash);
    }
  });

  it('registers the compile-mode status chapter without claiming browser AOT', () => {
    const slug = 'sv/compile-mode-status';
    const dir = path.join(root, slug);
    const description = readFileSync(path.join(dir, 'description.html'), 'utf8');
    const source = readFileSync(path.join(dir, 'compile_mode_status.sv'), 'utf8');
    const solution = readFileSync(path.join(dir, 'compile_mode_status.sol.sv'), 'utf8');
    expect(meta[slug]?.runner ?? 'sim').toBe('sim');
    expect(meta[slug]?.focus).toBe('/src/compile_mode_status.sv');
    expect(source).toContain('assign sum = left - right;');
    expect(solution).toContain('assign sum = left + right;');
    expect(description).toContain('--mode=compile');
    expect(description).toContain('0/5');
    expect(description).toContain('daily.sh d3');
    expect(description).toContain('pinned WASM');
  });

  it('binds compile-mode refdiff receipts to committed source blobs', () => {
    const dir = path.join(root, 'sv/compile-mode-status');
    for (const [variant, filename] of [
      ['starter', 'compile_mode_status.sv'],
      ['solution', 'compile_mode_status.sol.sv']
    ]) {
      const sourcePath = path.join(dir, filename);
      const sourceHash = createHash('sha256')
        .update(readFileSync(sourcePath))
        .digest('hex');
      const receipt = JSON.parse(readFileSync(
        path.resolve(process.cwd(), `artifacts/tutorial/compile-mode-status/${variant}-refdiff.json`),
        'utf8'
      ));
      expect(receipt.source).toBe(sourcePath);
      expect(receipt.sha256).toBe(sourceHash);
      expect(receipt.refdiff_cache_key).toMatch(/^[0-9a-f]{64}$/);
    }
  });
});
