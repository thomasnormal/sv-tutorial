import { describe, expect, it } from 'vitest';
import { normalizeVcd } from './mox-adapter.js';

describe('VCD normalization', () => {
  it('preserves standard vector widths and known scalar values', () => {
    const vcd = `$scope module tb $end
$var reg 8 # count $end
$var reg 1 ! en $end
$upscope $end
$enddefinitions $end
#0
b00000000 #
0!
#5
b00000001 #
1!
`;

    const normalized = normalizeVcd(vcd);
    expect(normalized).toContain('$var reg 8 # count $end');
    expect(normalized).toContain('b00000001 #');
    expect(normalized).toContain('1!');
    expect(normalized).not.toContain('$var reg 4 # count $end');
    expect(normalized).not.toContain('x!');
  });
});
