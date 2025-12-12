import { IntegerInterpolateStrategy } from '@/com/techlloyd/janus/generators/interpolate/IntegerInterpolateStrategy';
import { RNG } from '@/com/techlloyd/janus/RNG';

describe('IntegerInterpolateStrategy', () => {
  const strategy = new IntegerInterpolateStrategy();

  it('should generate integers within range', () => {
    const rng: RNG = { random: () => Math.random() };

    for (let i = 0; i < 100; i++) {
      const value = strategy.interpolate(0, 10, rng);
      expect(Number.isInteger(value)).toBe(true);
      expect(value).toBeGreaterThanOrEqual(0);
      expect(value).toBeLessThanOrEqual(10);
    }
  });

  it('should generate minimum value when RNG returns 0', () => {
    const rng: RNG = { random: () => 0.0 };
    expect(strategy.interpolate(5, 15, rng)).toBe(5);
    expect(strategy.interpolate(-10, 10, rng)).toBe(-10);
    expect(strategy.interpolate(0, 0, rng)).toBe(0);
  });

  it('should generate maximum value when RNG returns close to 1', () => {
    const rng: RNG = { random: () => 0.99999 };
    expect(strategy.interpolate(5, 15, rng)).toBe(15);
    expect(strategy.interpolate(-10, 10, rng)).toBe(10);
    expect(strategy.interpolate(0, 100, rng)).toBe(100);
  });

  it('should generate all values in small range', () => {
    const rng: RNG = { random: () => Math.random() };
    const generatedValues = new Set<number>();

    for (let i = 0; i < 500; i++) {
      generatedValues.add(strategy.interpolate(0, 3, rng));
    }

    expect(generatedValues.has(0)).toBe(true);
    expect(generatedValues.has(1)).toBe(true);
    expect(generatedValues.has(2)).toBe(true);
    expect(generatedValues.has(3)).toBe(true);
    expect(generatedValues.size).toBe(4);
  });

  it('should handle single value range (min === max)', () => {
    const rng: RNG = { random: () => Math.random() };

    for (let i = 0; i < 10; i++) {
      expect(strategy.interpolate(42, 42, rng)).toBe(42);
    }
  });

  it('should handle negative ranges', () => {
    const rng: RNG = { random: () => Math.random() };

    for (let i = 0; i < 50; i++) {
      const value = strategy.interpolate(-10, -5, rng);
      expect(Number.isInteger(value)).toBe(true);
      expect(value).toBeGreaterThanOrEqual(-10);
      expect(value).toBeLessThanOrEqual(-5);
    }
  });

  it('should handle zero crossing range', () => {
    const rng: RNG = { random: () => Math.random() };
    const generatedValues = new Set<number>();

    for (let i = 0; i < 1000; i++) {
      generatedValues.add(strategy.interpolate(-2, 2, rng));
    }

    expect(generatedValues.has(-2)).toBe(true);
    expect(generatedValues.has(-1)).toBe(true);
    expect(generatedValues.has(0)).toBe(true);
    expect(generatedValues.has(1)).toBe(true);
    expect(generatedValues.has(2)).toBe(true);
  });

  it('should distribute values uniformly', () => {
    const rng: RNG = { random: () => Math.random() };
    const counts = new Map<number, number>();
    const iterations = 10000;

    for (let i = 0; i < iterations; i++) {
      const value = strategy.interpolate(0, 4, rng);
      counts.set(value, (counts.get(value) || 0) + 1);
    }

    // Each value should appear roughly 20% of the time (within tolerance)
    const expectedCount = iterations / 5;
    for (let i = 0; i <= 4; i++) {
      const count = counts.get(i) || 0;
      expect(count).toBeGreaterThan(expectedCount * 0.7);
      expect(count).toBeLessThan(expectedCount * 1.3);
    }
  });
});

