/**
 * Static checks over the lesson sources (starter, solution and description
 * snippets). These catch code that a strict, standard-conforming tool rejects
 * even when a lenient one happens to accept it.
 */

import { describe, it, expect } from 'vitest';
import { readdirSync, readFileSync, statSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const LESSONS_DIR = path.dirname(fileURLToPath(import.meta.url));

function walk(dir) {
  const out = [];
  for (const name of readdirSync(dir)) {
    const full = path.join(dir, name);
    if (statSync(full).isDirectory()) out.push(...walk(full));
    else out.push(full);
  }
  return out;
}

const SOURCES = walk(LESSONS_DIR)
  .filter((f) => f.endsWith('.sv') || f.endsWith('description.html'))
  .map((f) => ({ rel: path.relative(LESSONS_DIR, f), text: readFileSync(f, 'utf8') }));

const DATA_TYPE = String.raw`(?:bit|logic|reg|byte|shortint|int|longint|integer|string|real)`;

describe('lesson sources', () => {
  // IEEE 1800-2023 §6.5: "Data shall be declared before they are used".
  // The `uvm_field_*` macros expand to code that references the field, so the
  // field declaration has to come first (Xcelium: *E,UNDIDN).
  it('declare every UVM field before its `uvm_field_* macro', () => {
    const problems = [];
    for (const { rel, text } of SOURCES) {
      for (const m of text.matchAll(/`uvm_field_\w+\(\s*(\w+)/g)) {
        const name = m[1];
        const decl = new RegExp(
          String.raw`^[ \t]*(?:rand[c]?\s+)?${DATA_TYPE}\b[^;\n]*\b${name}\b`,
          'm'
        ).exec(text);
        if (!decl || decl.index > m.index) problems.push(`${rel}: ${name}`);
      }
    }
    expect(problems).toEqual([]);
  });

  // IEEE 1800.2-2020 defines neither the uvm_top global nor a public
  // finish_on_completion field; the portable API is
  // uvm_root::get().set_finish_on_completion() (F.7.2.2, F.7.3.4).
  // Xcelium's IEEE UVM rejects uvm_top with *E,CUVUNF.
  it('use only IEEE 1800.2 uvm_root API', () => {
    const offenders = SOURCES.filter(({ text }) =>
      /\buvm_top\b|\.finish_on_completion\b/.test(text)
    ).map(({ rel }) => rel);
    expect(offenders).toEqual([]);
  });

  // An assumption is a promise about the environment (§16.14.2), so it may
  // only name the module's inputs. One on the design's own state is X at
  // the first clock edge and fails in simulation.
  it('assume only module inputs', () => {
    const problems = [];
    for (const { rel, text } of SOURCES.filter(({ rel }) => rel.endsWith('.sv'))) {
      const inputs = new Set();
      for (const m of text.matchAll(/\binput\b([\s\S]*?)(?=\b(?:input|output|inout)\b|\);)/g)) {
        const decl = m[1].replace(/\/\/.*$/gm, '').replace(/\[[^\]]*\]/g, '');
        for (const name of decl.match(/\b[A-Za-z_]\w*\b/g) ?? []) inputs.add(name);
      }
      for (const m of text.matchAll(/^[^\/\n]*\bassume\s+property\s*\(\s*@\([^)]*\)([^;]*)\);/gm)) {
        const names = m[1].match(/\b[A-Za-z_]\w*\b/g) ?? [];
        for (const name of names) if (!inputs.has(name)) problems.push(`${rel}: ${name}`);
      }
    }
    expect(problems).toEqual([]);
  });
});
