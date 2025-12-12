import { Infinity, NegativeInfinity } from '@/com/techlloyd/janus/combinators/Infinity';
import { DomainType, RNG, Generator } from '@/com/techlloyd/janus/index';

describe('Infinity', () => {
  describe('validation', () => {
    it('should validate positive Infinity', () => {
      const validator = Infinity();
      expect(validator.validate(globalThis.Infinity).valid).toBe(true);
    });

    it('should reject negative Infinity', () => {
      const validator = Infinity();
      const result = validator.validate(-globalThis.Infinity);
      expect(result.valid).toBe(false);
    });

    it('should reject finite numbers', () => {
      const validator = Infinity();
      expect(validator.validate(0).valid).toBe(false);
      expect(validator.validate(1e308).valid).toBe(false);
      expect(validator.validate(-1e308).valid).toBe(false);
    });

    it('should reject non-numbers', () => {
      const validator = Infinity();
      expect(validator.validate('Infinity').valid).toBe(false);
      expect(validator.validate(null).valid).toBe(false);
      expect(validator.validate(undefined).valid).toBe(false);
    });

    it('should return Infinity as the validated value', () => {
      const validator = Infinity();
      const result = validator.validate(globalThis.Infinity);
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe(globalThis.Infinity);
      }
    });
  });

  describe('domain', () => {
    it('should expose a FiniteDomain', () => {
      const validator = Infinity();
      expect(validator.domain.type).toBe(DomainType.FINITE_DOMAIN);
    });
  });

  describe('generation', () => {
    it('should generate Infinity', () => {
      const validator = Infinity();
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);
      
      const value = generator.generate(validator.domain);
      expect(value).toBe(globalThis.Infinity);
    });
  });
});

describe('NegativeInfinity', () => {
  describe('validation', () => {
    it('should validate negative Infinity', () => {
      const validator = NegativeInfinity();
      expect(validator.validate(-globalThis.Infinity).valid).toBe(true);
    });

    it('should reject positive Infinity', () => {
      const validator = NegativeInfinity();
      const result = validator.validate(globalThis.Infinity);
      expect(result.valid).toBe(false);
    });

    it('should reject finite numbers', () => {
      const validator = NegativeInfinity();
      expect(validator.validate(0).valid).toBe(false);
      expect(validator.validate(-1e308).valid).toBe(false);
    });

    it('should return -Infinity as the validated value', () => {
      const validator = NegativeInfinity();
      const result = validator.validate(-globalThis.Infinity);
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe(-globalThis.Infinity);
      }
    });
  });

  describe('generation', () => {
    it('should generate -Infinity', () => {
      const validator = NegativeInfinity();
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);
      
      const value = generator.generate(validator.domain);
      expect(value).toBe(-globalThis.Infinity);
    });
  });
});

