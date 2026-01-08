import { Integer } from '@/com/techlloyd/janus/combinators/Integer';
import { Generator, RNG, ContiguousDomain } from '@/com/techlloyd/janus/index';
import { DomainType } from '@janus-validator/domain';

describe('Integer validator', () => {
  it('should validate valid integers', () => {
    const validator = Integer();
    expect(validator.validate(0).valid).toBe(true);
    expect(validator.validate(1).valid).toBe(true);
    expect(validator.validate(-1).valid).toBe(true);
    expect(validator.validate(42).valid).toBe(true);
    expect(validator.validate(-1000).valid).toBe(true);
  });

  it('should reject non-number values', () => {
    const validator = Integer();
    expect(validator.validate('123').valid).toBe(false);
    expect(validator.validate(null).valid).toBe(false);
    expect(validator.validate(undefined).valid).toBe(false);
    expect(validator.validate({}).valid).toBe(false);
    expect(validator.validate(true).valid).toBe(false);
  });

  it('should reject non-integer numbers', () => {
    const validator = Integer();
    expect(validator.validate(1.5).valid).toBe(false);
    expect(validator.validate(0.1).valid).toBe(false);
    expect(validator.validate(-3.14).valid).toBe(false);
  });

  it('should reject non-finite numbers', () => {
    const validator = Integer();
    expect(validator.validate(Infinity).valid).toBe(false);
    expect(validator.validate(-Infinity).valid).toBe(false);
    expect(validator.validate(NaN).valid).toBe(false);
  });

  it('should validate integers within range', () => {
    const validator = Integer(0, 10);
    expect(validator.validate(0).valid).toBe(true);
    expect(validator.validate(5).valid).toBe(true);
    expect(validator.validate(10).valid).toBe(true);
    expect(validator.validate(-1).valid).toBe(false);
    expect(validator.validate(11).valid).toBe(false);
  });

  it('should validate with minimum only', () => {
    const validator = Integer(5);
    expect(validator.validate(5).valid).toBe(true);
    expect(validator.validate(100).valid).toBe(true);
    expect(validator.validate(4).valid).toBe(false);
  });

  it('should validate negative ranges', () => {
    const validator = Integer(-10, -1);
    expect(validator.validate(-10).valid).toBe(true);
    expect(validator.validate(-5).valid).toBe(true);
    expect(validator.validate(-1).valid).toBe(true);
    expect(validator.validate(0).valid).toBe(false);
    expect(validator.validate(-11).valid).toBe(false);
  });

  it('should expose a contiguous domain', () => {
    const validator = Integer(0, 100);
    expect(validator.domain).toBeDefined();
    expect(validator.domain.kind).toBe(DomainType.CONTIGUOUS);
    const domain = validator.domain as ContiguousDomain<number>;
    expect(domain.min).toBe(0);
    expect(domain.max).toBe(100);
  });

  // Edge cases
  it('should validate single value range (min === max)', () => {
    const validator = Integer(42, 42);
    expect(validator.validate(42).valid).toBe(true);
    expect(validator.validate(41).valid).toBe(false);
    expect(validator.validate(43).valid).toBe(false);
  });

  it('should validate zero crossing range', () => {
    const validator = Integer(-5, 5);
    expect(validator.validate(-5).valid).toBe(true);
    expect(validator.validate(0).valid).toBe(true);
    expect(validator.validate(5).valid).toBe(true);
    expect(validator.validate(-6).valid).toBe(false);
    expect(validator.validate(6).valid).toBe(false);
  });

  it('should validate at safe integer boundaries', () => {
    const validator = Integer();
    expect(validator.validate(Number.MAX_SAFE_INTEGER).valid).toBe(true);
    expect(validator.validate(Number.MIN_SAFE_INTEGER).valid).toBe(true);
  });

  it('should validate with zero as boundary', () => {
    const validatorMin = Integer(0, 10);
    expect(validatorMin.validate(0).valid).toBe(true);
    expect(validatorMin.validate(-1).valid).toBe(false);

    const validatorMax = Integer(-10, 0);
    expect(validatorMax.validate(0).valid).toBe(true);
    expect(validatorMax.validate(1).valid).toBe(false);
  });

  it('should reject values just outside boundaries', () => {
    const validator = Integer(10, 20);
    expect(validator.validate(9).valid).toBe(false);
    expect(validator.validate(10).valid).toBe(true);
    expect(validator.validate(20).valid).toBe(true);
    expect(validator.validate(21).valid).toBe(false);
  });

  it('should reject floats that are very close to integers', () => {
    const validator = Integer();
    expect(validator.validate(1.0000000001).valid).toBe(false);
    expect(validator.validate(0.9999999999).valid).toBe(false);
    expect(validator.validate(-1.0000000001).valid).toBe(false);
  });

  it('should accept integer-valued floats (1.0, 2.0, etc)', () => {
    const validator = Integer();
    expect(validator.validate(1.0).valid).toBe(true);
    expect(validator.validate(-1.0).valid).toBe(true);
    expect(validator.validate(0.0).valid).toBe(true);
  });

  it('should accept -0 as distinct from 0 when checking type', () => {
    const validator = Integer();
    // -0 is still a valid integer in JavaScript
    expect(validator.validate(-0).valid).toBe(true);
  });
});

describe('Integer domain generation', () => {
  it('should generate valid integers using Generator', () => {
    const validator = Integer(0, 100);
    const rng: RNG = {
      random: () => Math.random(),
    };
    const generator = new Generator(rng);

    const value = generator.generate(validator.domain);
    expect(typeof value).toBe('number');
    expect(Number.isInteger(value)).toBe(true);
    
    // Generated value should pass validation
    const result = validator.validate(value);
    expect(result.valid).toBe(true);
  });

  it('should generate integers within range', () => {
    const validator = Integer(10, 20);
    const rng: RNG = {
      random: () => Math.random(),
    };
    const generator = new Generator(rng);

    // Generate multiple values and verify they all meet constraints
    for (let i = 0; i < 100; i++) {
      const value = generator.generate(validator.domain);
      const result = validator.validate(value);
      expect(result.valid).toBe(true);
      expect(value).toBeGreaterThanOrEqual(10);
      expect(value).toBeLessThanOrEqual(20);
      expect(Number.isInteger(value)).toBe(true);
    }
  });

  it('should generate minimum value when RNG returns 0', () => {
    const validator = Integer(5, 15);
    const rng: RNG = {
      random: () => 0.0,
    };
    const generator = new Generator(rng);

    const value = generator.generate(validator.domain);
    expect(value).toBe(5);
  });

  it('should generate maximum value when RNG returns close to 1', () => {
    const validator = Integer(5, 15);
    const rng: RNG = {
      random: () => 0.99999,
    };
    const generator = new Generator(rng);

    const value = generator.generate(validator.domain);
    expect(value).toBe(15);
  });

  it('should generate all values in range over many iterations', () => {
    const validator = Integer(0, 5);
    const rng: RNG = {
      random: () => Math.random(),
    };
    const generator = new Generator(rng);

    const generatedValues = new Set<number>();
    for (let i = 0; i < 1000; i++) {
      generatedValues.add(generator.generate(validator.domain));
    }

    // Should have generated all values 0-5
    expect(generatedValues.has(0)).toBe(true);
    expect(generatedValues.has(1)).toBe(true);
    expect(generatedValues.has(2)).toBe(true);
    expect(generatedValues.has(3)).toBe(true);
    expect(generatedValues.has(4)).toBe(true);
    expect(generatedValues.has(5)).toBe(true);
  });

  it('should generate negative integers', () => {
    const validator = Integer(-10, -5);
    const rng: RNG = {
      random: () => Math.random(),
    };
    const generator = new Generator(rng);

    for (let i = 0; i < 50; i++) {
      const value = generator.generate(validator.domain);
      const result = validator.validate(value);
      expect(result.valid).toBe(true);
      expect(value).toBeGreaterThanOrEqual(-10);
      expect(value).toBeLessThanOrEqual(-5);
    }
  });

  it('should generate values that pass validation', () => {
    const validator = Integer(-100, 100);
    const rng: RNG = {
      random: () => Math.random(),
    };
    const generator = new Generator(rng);

    // Generate multiple values and verify they all pass validation
    for (let i = 0; i < 100; i++) {
      const value = generator.generate(validator.domain);
      const result = validator.validate(value);
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe(value);
      }
    }
  });

  // Edge cases for generation
  it('should generate single value when min === max', () => {
    const validator = Integer(42, 42);
    const rng: RNG = {
      random: () => Math.random(),
    };
    const generator = new Generator(rng);

    for (let i = 0; i < 10; i++) {
      const value = generator.generate(validator.domain);
      expect(value).toBe(42);
    }
  });

  it('should generate values in zero crossing range', () => {
    const validator = Integer(-3, 3);
    const rng: RNG = {
      random: () => Math.random(),
    };
    const generator = new Generator(rng);

    const generatedValues = new Set<number>();
    for (let i = 0; i < 1000; i++) {
      generatedValues.add(generator.generate(validator.domain));
    }

    // Should have generated all values -3 to 3
    expect(generatedValues.has(-3)).toBe(true);
    expect(generatedValues.has(-2)).toBe(true);
    expect(generatedValues.has(-1)).toBe(true);
    expect(generatedValues.has(0)).toBe(true);
    expect(generatedValues.has(1)).toBe(true);
    expect(generatedValues.has(2)).toBe(true);
    expect(generatedValues.has(3)).toBe(true);
  });

  it('should handle edge RNG values', () => {
    const validator = Integer(0, 10);
    
    // Test RNG returning exactly 0
    const rng0: RNG = { random: () => 0 };
    const gen0 = new Generator(rng0);
    expect(gen0.generate(validator.domain)).toBe(0);

    // Test RNG returning value very close to 1
    const rng1: RNG = { random: () => 1 - Number.EPSILON };
    const gen1 = new Generator(rng1);
    const value = gen1.generate(validator.domain);
    expect(value).toBeGreaterThanOrEqual(0);
    expect(value).toBeLessThanOrEqual(10);
  });

  it('should generate uniform distribution across range', () => {
    const validator = Integer(0, 9);
    const rng: RNG = {
      random: () => Math.random(),
    };
    const generator = new Generator(rng);

    const counts = new Map<number, number>();
    const iterations = 10000;
    
    for (let i = 0; i < iterations; i++) {
      const value = generator.generate(validator.domain);
      counts.set(value, (counts.get(value) || 0) + 1);
    }

    // Each value should appear roughly 10% of the time (within 5% tolerance)
    const expectedCount = iterations / 10;
    for (let i = 0; i <= 9; i++) {
      const count = counts.get(i) || 0;
      expect(count).toBeGreaterThan(expectedCount * 0.7);
      expect(count).toBeLessThan(expectedCount * 1.3);
    }
  });
});

