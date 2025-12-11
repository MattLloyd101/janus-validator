import { FloatInterpolateStrategy } from '@/com/techlloyd/janus/domains/interpolate/FloatInterpolateStrategy';
import { RNG } from '@/com/techlloyd/janus/RNG';

describe('FloatInterpolateStrategy', () => {
  const strategy = new FloatInterpolateStrategy();

  it('should generate floats within range', () => {
    const rng: RNG = { random: () => Math.random() };

    for (let i = 0; i < 100; i++) {
      const value = strategy.interpolate(0, 1, rng);
      expect(value).toBeGreaterThanOrEqual(0);
      expect(value).toBeLessThan(1);
    }
  });

  it('should generate minimum value when RNG returns 0', () => {
    const rng: RNG = { random: () => 0.0 };
    expect(strategy.interpolate(0, 1, rng)).toBe(0);
    expect(strategy.interpolate(10, 20, rng)).toBe(10);
    expect(strategy.interpolate(-5, 5, rng)).toBe(-5);
  });

  it('should generate value approaching max when RNG returns close to 1', () => {
    const rng: RNG = { random: () => 0.99999 };
    const value = strategy.interpolate(0, 100, rng);
    expect(value).toBeCloseTo(99.999, 2);
  });

  it('should scale to range correctly', () => {
    const rng: RNG = { random: () => 0.5 };
    expect(strategy.interpolate(0, 100, rng)).toBe(50);
    expect(strategy.interpolate(100, 200, rng)).toBe(150);
    expect(strategy.interpolate(-50, 50, rng)).toBe(0);
  });

  it('should handle single value range (min === max)', () => {
    const rng: RNG = { random: () => Math.random() };

    for (let i = 0; i < 10; i++) {
      expect(strategy.interpolate(42.5, 42.5, rng)).toBe(42.5);
    }
  });

  it('should handle negative ranges', () => {
    const rng: RNG = { random: () => Math.random() };

    for (let i = 0; i < 50; i++) {
      const value = strategy.interpolate(-10.5, -5.5, rng);
      expect(value).toBeGreaterThanOrEqual(-10.5);
      expect(value).toBeLessThan(-5.5);
    }
  });

  it('should handle zero crossing range', () => {
    const rng: RNG = { random: () => Math.random() };

    for (let i = 0; i < 50; i++) {
      const value = strategy.interpolate(-1, 1, rng);
      expect(value).toBeGreaterThanOrEqual(-1);
      expect(value).toBeLessThan(1);
    }
  });

  it('should linearly interpolate based on RNG value', () => {
    expect(strategy.interpolate(0, 100, { random: () => 0.0 })).toBe(0);
    expect(strategy.interpolate(0, 100, { random: () => 0.25 })).toBe(25);
    expect(strategy.interpolate(0, 100, { random: () => 0.5 })).toBe(50);
    expect(strategy.interpolate(0, 100, { random: () => 0.75 })).toBe(75);
  });

  it('should handle large ranges', () => {
    const rng: RNG = { random: () => 0.5 };
    const value = strategy.interpolate(0, 1e10, rng);
    expect(value).toBe(5e9);
  });

  it('should handle small ranges', () => {
    const rng: RNG = { random: () => 0.5 };
    const value = strategy.interpolate(0, 0.001, rng);
    expect(value).toBeCloseTo(0.0005, 6);
  });
});

