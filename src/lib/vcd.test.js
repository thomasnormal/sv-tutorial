import { describe, expect, it } from 'vitest';
import { firstTransitioningVar } from './vcd.js';

const HEADER = `$timescale 1ns $end
$scope module tb $end
$var reg 4 ) addr $end
$var reg 1 ( clk $end
$upscope $end
$enddefinitions $end
`;

describe('firstTransitioningVar', () => {
  it('picks the earliest change after the initial $dumpvars values', () => {
    const vcd = `${HEADER}#0\n$dumpvars\nb0 )\n0(\n$end\n#5\n1(\n#6\nb10 )\n`;
    expect(firstTransitioningVar(vcd)?.fullPath).toBe('tb.clk');
  });

  it('counts changes at the dump time that follow the $dumpvars block', () => {
    // addr changes at time 0, right after its initial value is dumped.
    const vcd = `${HEADER}#0\n$dumpvars\nb0 )\n0(\n$end\nb10 )\n#5\n1(\n`;
    expect(firstTransitioningVar(vcd)?.fullPath).toBe('tb.addr');
  });

  it('reads the dump time when the timestamp is written inside $dumpvars', () => {
    // Mox writes `#0` inside the $dumpvars block (not allowed by the grammar
    // in IEEE 1800-2023 §21.7.2.1, but it should not change the result).
    const vcd = `${HEADER}$dumpvars\n#0\nb0 )\n0(\n$end\nb10 )\n#5\n1(\n`;
    expect(firstTransitioningVar(vcd)?.fullPath).toBe('tb.addr');
  });
});
