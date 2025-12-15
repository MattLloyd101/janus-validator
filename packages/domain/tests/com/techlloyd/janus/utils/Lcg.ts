/**
 * Lightweight deterministic PRNG for tests (so property-test failures are reproducible).
 */
export class Lcg {
  private state: number;

  constructor(seed = 0x12345678) {
    this.state = seed >>> 0;
  }

  nextU32(): number {
    // Numerical Recipes LCG constants
    this.state = (1664525 * this.state + 1013904223) >>> 0;
    return this.state;
  }

  nextFloat(): number {
    return this.nextU32() / 0x1_0000_0000;
  }

  int(min: number, max: number): number {
    const a = Math.min(min, max);
    const b = Math.max(min, max);
    const span = b - a + 1;
    return a + Math.floor(this.nextFloat() * span);
  }

  bool(pTrue = 0.5): boolean {
    return this.nextFloat() < pTrue;
  }
}


