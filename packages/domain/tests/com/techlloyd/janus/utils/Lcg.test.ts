import { Lcg } from './Lcg';

describe('Lcg (test utils)', () => {
  it('covers default parameters and basic behavior', () => {
    // Default seed path (covers default-arg branch)
    const rng0 = new Lcg();
    const a = rng0.nextU32();
    const b = rng0.nextU32();
    expect(a).not.toBe(b);

    // Explicit seed path
    const rng1 = new Lcg(123);
    expect(rng1.nextU32()).toBeDefined();

    // Default pTrue path + explicit pTrue path
    expect(typeof rng0.bool()).toBe('boolean');
    expect(rng0.bool(0)).toBe(false);

    // Reversed min/max path (int normalizes)
    const x = rng0.int(10, 5);
    expect(x).toBeGreaterThanOrEqual(5);
    expect(x).toBeLessThanOrEqual(10);
  });
});


