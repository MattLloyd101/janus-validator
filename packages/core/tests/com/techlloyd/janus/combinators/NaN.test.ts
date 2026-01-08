import { NaN } from '@/com/techlloyd/janus/combinators/NaN';
import { DomainType, RNG, Generator } from '@/com/techlloyd/janus/index';

describe('NaN', () => {
  describe('validation', () => {
    it('should validate NaN', () => {
      const validator = NaN();
      expect(validator.validate(globalThis.NaN).valid).toBe(true);
    });

    it('should validate expressions that produce NaN', () => {
      const validator = NaN();
      expect(validator.validate(0 / 0).valid).toBe(true);
      expect(validator.validate(globalThis.Number.NaN).valid).toBe(true);
      expect(validator.validate(Math.sqrt(-1)).valid).toBe(true);
      expect(validator.validate(parseFloat('not a number')).valid).toBe(true);
    });

    it('should reject numbers', () => {
      const validator = NaN();
      expect(validator.validate(0).valid).toBe(false);
      expect(validator.validate(123).valid).toBe(false);
      expect(validator.validate(-456.789).valid).toBe(false);
    });

    it('should reject Infinity', () => {
      const validator = NaN();
      expect(validator.validate(globalThis.Infinity).valid).toBe(false);
      expect(validator.validate(-globalThis.Infinity).valid).toBe(false);
    });

    it('should reject non-numbers', () => {
      const validator = NaN();
      expect(validator.validate('NaN').valid).toBe(false);
      expect(validator.validate(null).valid).toBe(false);
      expect(validator.validate(undefined).valid).toBe(false);
    });

    it('should return NaN as the validated value', () => {
      const validator = NaN();
      const result = validator.validate(globalThis.NaN);
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(globalThis.Number.isNaN(result.value)).toBe(true);
      }
    });
  });

  describe('domain', () => {
    it('should expose a FiniteDomain', () => {
      const validator = NaN();
      expect(validator.domain.kind).toBe(DomainType.FINITE);
    });
  });

  describe('generation', () => {
    it('should generate NaN', () => {
      const validator = NaN();
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);
      
      const value = generator.generate(validator.domain);
      expect(globalThis.Number.isNaN(value)).toBe(true);
    });
  });
});

