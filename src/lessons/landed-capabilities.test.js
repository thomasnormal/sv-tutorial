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
  ['sv/sequential-udp-init', 'sequential_udp'],
  ['sv/wide-readmem', 'wide_readmem'],
  ['sv/coverage-option-text', 'coverage_option_text']
];

function receiptSourceMatches(receiptSource, sourcePath) {
  const relativeSource = path
    .relative(process.cwd(), sourcePath)
    .split(path.sep)
    .join('/');
  return receiptSource.replaceAll('\\', '/').endsWith(relativeSource);
}

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
      expect(receiptSourceMatches(receipt.source, sourcePath)).toBe(true);
      expect(receipt.sha256).toBe(sourceHash);
    }
  });

  it('accepts receipt source paths from another checkout root', () => {
    const sourcePath = path.join(root, 'sv/sequential-udp-init/sequential_udp.sv');
    expect(receiptSourceMatches(
      '/home/runner/work/sv-tutorial/sv-tutorial/src/lessons/sv/sequential-udp-init/sequential_udp.sv',
      sourcePath
    )).toBe(true);
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
    expect(description).toContain('a0c4488a587');
    expect(description).toContain('NEW-REFUSAL');
    expect(readFileSync(
      path.resolve(process.cwd(), 'artifacts/tutorial/compile-mode-status/s4-d2-report.md'),
      'utf8'
    )).toContain('Compile PASS: 0/5 rows');
  });

  it('calibrates the MQ93 clocking sampler exercise', () => {
    const dir = path.join(root, 'sv/clocking-sampler-retention');
    const starter = readFileSync(path.join(dir, 'clocking_sampler.sv'), 'utf8');
    const solution = readFileSync(path.join(dir, 'clocking_sampler.sol.sv'), 'utf8');
    const description = readFileSync(path.join(dir, 'description.html'), 'utf8');
    expect(meta['sv/clocking-sampler-retention']?.runner ?? 'sim').toBe('sim');
    expect(meta['sv/clocking-sampler-retention']?.focus).toBe('/src/clocking_sampler.sv');
    expect(starter).toContain('input sig;');
    expect(solution).toContain('input #0 sig;');
    expect(description).toContain('§14.13');
    expect(description).toContain('3b1760ff203');
  });

  it('binds clocking sampler refdiff receipts to committed source blobs', () => {
    const dir = path.join(root, 'sv/clocking-sampler-retention');
    for (const [variant, filename] of [
      ['starter', 'clocking_sampler.sv'],
      ['solution', 'clocking_sampler.sol.sv']
    ]) {
      const sourcePath = path.join(dir, filename);
      const sourceHash = createHash('sha256')
        .update(readFileSync(sourcePath))
        .digest('hex');
      const receipt = JSON.parse(readFileSync(
        path.resolve(process.cwd(), `artifacts/tutorial/clocking-sampler-retention/${variant}-refdiff.json`),
        'utf8'
      ));
      expect(receiptSourceMatches(receipt.source, sourcePath)).toBe(true);
      expect(receipt.sha256).toBe(sourceHash);
      expect(receipt.refdiff_cache_key).toMatch(/^[0-9a-f]{64}$/);
    }
  });

  it('records the protected-envelope callback boundary without claiming decryption', () => {
    const dir = path.join(root, 'sv/protected-envelope-boundary');
    const starter = readFileSync(path.join(dir, 'protected_envelope.sv'), 'utf8');
    const solution = readFileSync(path.join(dir, 'protected_envelope.sol.sv'), 'utf8');
    const description = readFileSync(path.join(dir, 'description.html'), 'utf8');
    expect(meta['sv/protected-envelope-boundary']?.runner ?? 'sim').toBe('sim');
    expect(meta['sv/protected-envelope-boundary']?.focus).toBe('/src/protected_envelope.sv');
    expect(starter).not.toContain('//pragma protect end_protected');
    expect(solution).toContain('//pragma protect end_protected');
    expect(description).toContain('§§34.2, 34.3, 34.4, 34.5.3, and 34.5.4');
    expect(description).toContain('c3799f427f1');
    const receipt = JSON.parse(readFileSync(
      path.resolve(process.cwd(), 'artifacts/tutorial/protected-envelope-boundary/solution-refdiff.json'),
      'utf8'
    ));
    expect(receipt.category).toBe('reference_only_fail');
  });

  it('binds protected-envelope refdiff receipts to committed source blobs', () => {
    const dir = path.join(root, 'sv/protected-envelope-boundary');
    for (const [variant, filename] of [
      ['starter', 'protected_envelope.sv'],
      ['solution', 'protected_envelope.sol.sv']
    ]) {
      const sourcePath = path.join(dir, filename);
      const sourceHash = createHash('sha256')
        .update(readFileSync(sourcePath))
        .digest('hex');
      const receipt = JSON.parse(readFileSync(
        path.resolve(process.cwd(), `artifacts/tutorial/protected-envelope-boundary/${variant}-refdiff.json`),
        'utf8'
      ));
      expect(receiptSourceMatches(receipt.source, sourcePath)).toBe(true);
      expect(receipt.sha256).toBe(sourceHash);
      expect(receipt.refdiff_cache_key).toMatch(/^[0-9a-f]{64}$/);
    }
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
      expect(receiptSourceMatches(receipt.source, sourcePath)).toBe(true);
      expect(receipt.sha256).toBe(sourceHash);
      expect(receipt.refdiff_cache_key).toMatch(/^[0-9a-f]{64}$/);
    }
  });

  it('registers the virtual-provider closure chapter and its landed behavior', () => {
    const slug = 'sv/virtual-provider-closure';
    const dir = path.join(root, slug);
    const description = readFileSync(path.join(dir, 'description.html'), 'utf8');
    const source = readFileSync(path.join(dir, 'virtual_provider.sv'), 'utf8');
    const solution = readFileSync(path.join(dir, 'virtual_provider.sol.sv'), 'utf8');
    expect(meta[slug]?.runner ?? 'sim').toBe('sim');
    expect(meta[slug]?.focus).toBe('/src/virtual_provider.sv');
    expect(source).toContain('implementation_id = 606;');
    expect(solution).toContain('implementation_id = 707;');
    expect(description).toContain('§8.20');
    expect(description).toContain('§8.22');
    expect(description).toContain('3bc88e77921e');
    expect(solution).toContain('$display("PASS: virtual provider');
  });

  it('binds virtual-provider refdiff receipts to committed source blobs', () => {
    const dir = path.join(root, 'sv/virtual-provider-closure');
    for (const [variant, filename] of [
      ['starter', 'virtual_provider.sv'],
      ['solution', 'virtual_provider.sol.sv']
    ]) {
      const sourcePath = path.join(dir, filename);
      const sourceHash = createHash('sha256')
        .update(readFileSync(sourcePath))
        .digest('hex');
      const receipt = JSON.parse(readFileSync(
        path.resolve(process.cwd(), `artifacts/tutorial/virtual-provider-closure/${variant}-refdiff.json`),
        'utf8'
      ));
      expect(receiptSourceMatches(receipt.source, sourcePath)).toBe(true);
      expect(receipt.sha256).toBe(sourceHash);
      expect(receipt.refdiff_cache_key).toMatch(/^[0-9a-f]{64}$/);
    }
  });

  it('registers the wide four-state readmem chapter and its landed behavior', () => {
    const slug = 'sv/wide-readmem';
    const dir = path.join(root, slug);
    const starter = readFileSync(path.join(dir, 'wide_readmem.sv'), 'utf8');
    const solution = readFileSync(path.join(dir, 'wide_readmem.sol.sv'), 'utf8');
    const description = readFileSync(path.join(dir, 'description.html'), 'utf8');
    expect(meta[slug]?.runner ?? 'sim').toBe('sim');
    expect(meta[slug]?.focus).toBe('/src/wide_readmem.sv');
    expect(starter).toContain('logic [63:0] memory [0:2]');
    expect(solution).toContain('logic [64:0] memory [0:2]');
    expect(description).toContain('§21.4.1');
    expect(description).toContain('e7da9630dcd');
    expect(description).toContain('writable temporary directory');
    expect(solution).toContain('$display("PASS")');

    for (const [variant, filename] of [
      ['starter', 'wide_readmem.sv'],
      ['solution', 'wide_readmem.sol.sv']
    ]) {
      const sourcePath = path.join(dir, filename);
      const sourceHash = createHash('sha256')
        .update(readFileSync(sourcePath))
        .digest('hex');
      const receipt = JSON.parse(readFileSync(
        path.resolve(process.cwd(), `artifacts/tutorial/wide-readmem/${variant}-refdiff.json`),
        'utf8'
      ));
      expect(receiptSourceMatches(receipt.source, sourcePath)).toBe(true);
      expect(receipt.sha256).toBe(sourceHash);
      expect(receipt.refdiff_cache_key).toMatch(/^[0-9a-f]{64}$/);
    }
  });

  it('registers the coverage option text chapter and its landed behavior', () => {
    const slug = 'sv/coverage-option-text';
    const dir = path.join(root, slug);
    const starter = readFileSync(path.join(dir, 'coverage_option_text.sv'), 'utf8');
    const solution = readFileSync(path.join(dir, 'coverage_option_text.sol.sv'), 'utf8');
    const description = readFileSync(path.join(dir, 'description.html'), 'utf8');
    expect(meta[slug]?.runner ?? 'sim').toBe('sim');
    expect(meta[slug]?.focus).toBe('/src/coverage_option_text.sv');
    expect(starter).toContain('FAIL: starter rejected the empty default comment');
    expect(solution).toContain('coverage.option.comment = "runtime coverage comment"');
    expect(description).toContain('§19.7');
    expect(description).toContain('b481355f9fe');
    expect(solution).toContain('$display("PASS")');

    for (const [variant, filename] of [
      ['starter', 'coverage_option_text.sv'],
      ['solution', 'coverage_option_text.sol.sv']
    ]) {
      const sourcePath = path.join(dir, filename);
      const sourceHash = createHash('sha256')
        .update(readFileSync(sourcePath))
        .digest('hex');
      const receipt = JSON.parse(readFileSync(
        path.resolve(process.cwd(), `artifacts/tutorial/coverage-option-text/${variant}-refdiff.json`),
        'utf8'
      ));
      expect(receiptSourceMatches(receipt.source, sourcePath)).toBe(true);
      expect(receipt.sha256).toBe(sourceHash);
      expect(receipt.refdiff_cache_key).toMatch(/^[0-9a-f]{64}$/);
      expect(readFileSync(
        path.resolve(process.cwd(), `artifacts/tutorial/coverage-option-text/${variant}-source.sha256`),
        'utf8'
      ).trim()).toBe(sourceHash);
    }
  });
});
