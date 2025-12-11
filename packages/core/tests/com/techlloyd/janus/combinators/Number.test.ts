import { Number } from '@/com/techlloyd/janus/combinators/Number';
import { DomainType, ContiguousType, ContiguousDomain, RNG, Generator } from '@/com/techlloyd/janus/index';

describe('Number', () => {
  describe('validation', () => {
    it('should validate numbers within range', () => {
      const validator = Number(0, 100);

      expect(validator.validate(0).valid).toBe(true);
      expect(validator.validate(50).valid).toBe(true);
      expect(validator.validate(100).valid).toBe(true);
      expect(validator.validate(50.5).valid).toBe(true);
      expect(validator.validate(0.001).valid).toBe(true);
      expect(validator.validate(99.999).valid).toBe(true);
    });

    it('should reject numbers below minimum', () => {
      const validator = Number(0, 100);
      const result = validator.validate(-1);

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('less than minimum');
      }
    });

    it('should reject numbers above maximum', () => {
      const validator = Number(0, 100);
      const result = validator.validate(100.1);

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('greater than maximum');
      }
    });

    it('should reject non-number values', () => {
      const validator = Number();

      expect(validator.validate('123').valid).toBe(false);
      expect(validator.validate(true).valid).toBe(false);
      expect(validator.validate(null).valid).toBe(false);
      expect(validator.validate(undefined).valid).toBe(false);
      expect(validator.validate({}).valid).toBe(false);
    });

    it('should reject non-finite numbers', () => {
      const validator = Number();

      expect(validator.validate(Infinity).valid).toBe(false);
      expect(validator.validate(-Infinity).valid).toBe(false);
      expect(validator.validate(NaN).valid).toBe(false);
    });

    it('should accept integers as valid numbers', () => {
      const validator = Number(0, 100);

      expect(validator.validate(50).valid).toBe(true);
      expect(validator.validate(0).valid).toBe(true);
      expect(validator.validate(100).valid).toBe(true);
    });

    it('should handle negative ranges', () => {
      const validator = Number(-100, -10);

      expect(validator.validate(-50).valid).toBe(true);
      expect(validator.validate(-100).valid).toBe(true);
      expect(validator.validate(-10).valid).toBe(true);
      expect(validator.validate(-9).valid).toBe(false);
      expect(validator.validate(0).valid).toBe(false);
    });

    it('should handle ranges spanning zero', () => {
      const validator = Number(-50, 50);

      expect(validator.validate(-50).valid).toBe(true);
      expect(validator.validate(0).valid).toBe(true);
      expect(validator.validate(50).valid).toBe(true);
      expect(validator.validate(-25.5).valid).toBe(true);
      expect(validator.validate(25.5).valid).toBe(true);
    });

    it('should work with default (unbounded) range', () => {
      const validator = Number();

      expect(validator.validate(0).valid).toBe(true);
      expect(validator.validate(1e100).valid).toBe(true);
      expect(validator.validate(-1e100).valid).toBe(true);
      expect(validator.validate(0.000001).valid).toBe(true);
    });

    it('should return the validated value', () => {
      const validator = Number(0, 100);
      const result = validator.validate(50.5);

      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe(50.5);
      }
    });
  });

  describe('domain', () => {
    it('should expose a ContiguousDomain with FLOAT type', () => {
      const validator = Number(0, 100);
      const domain = validator.domain as ContiguousDomain;

      expect(domain.type).toBe(DomainType.CONTIGUOUS_DOMAIN);
      expect(domain.contiguousType).toBe(ContiguousType.FLOAT);
    });

    it('should include min and max in domain', () => {
      const validator = Number(-50, 50);
      const domain = validator.domain as ContiguousDomain;

      expect(domain.min).toBe(-50);
      expect(domain.max).toBe(50);
    });
  });

  describe('generation', () => {
    it('should generate numbers within range', () => {
      const validator = Number(0, 100);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 100; i++) {
        const value = generator.generate(validator) as number;
        expect(typeof value).toBe('number');
        expect(value).toBeGreaterThanOrEqual(0);
        expect(value).toBeLessThanOrEqual(100);
      }
    });

    it('should generate floats, not just integers', () => {
      const validator = Number(0, 100);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      let foundFloat = false;
      for (let i = 0; i < 100; i++) {
        const value = generator.generate(validator) as number;
        if (!globalThis.Number.isInteger(value)) {
          foundFloat = true;
          break;
        }
      }
      expect(foundFloat).toBe(true);
    });

    it('should generate values that pass validation', () => {
      const validator = Number(-50, 50);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 100; i++) {
        const value = generator.generate(validator);
        const result = validator.validate(value);
        expect(result.valid).toBe(true);
      }
    });

    it('should generate boundary values', () => {
      const validator = Number(10, 20);
      
      // rng = 0 should give min
      const rngMin: RNG = { random: () => 0 };
      const genMin = new Generator(rngMin);
      expect(genMin.generate(validator)).toBe(10);

      // rng = 1 (or very close) should give max
      const rngMax: RNG = { random: () => 0.9999999999 };
      const genMax = new Generator(rngMax);
      const maxVal = genMax.generate(validator) as number;
      expect(maxVal).toBeGreaterThan(19.9);
      expect(maxVal).toBeLessThanOrEqual(20);
    });
  });

  describe('edge cases', () => {
    it('should handle very small ranges', () => {
      const validator = Number(0.5, 0.6);

      expect(validator.validate(0.5).valid).toBe(true);
      expect(validator.validate(0.55).valid).toBe(true);
      expect(validator.validate(0.6).valid).toBe(true);
      expect(validator.validate(0.49).valid).toBe(false);
      expect(validator.validate(0.61).valid).toBe(false);
    });

    it('should handle single-point range', () => {
      const validator = Number(5, 5);

      expect(validator.validate(5).valid).toBe(true);
      expect(validator.validate(5.0).valid).toBe(true);
      expect(validator.validate(4.999999999).valid).toBe(false);
      expect(validator.validate(5.000000001).valid).toBe(false);
    });

    it('should handle very large numbers', () => {
      const validator = Number(1e100, 1e200);

      expect(validator.validate(1e150).valid).toBe(true);
      expect(validator.validate(1e99).valid).toBe(false);
    });

    it('should handle very small numbers', () => {
      const validator = Number(1e-100, 1e-50);

      expect(validator.validate(1e-75).valid).toBe(true);
      expect(validator.validate(1e-101).valid).toBe(false);
    });
  });
});

