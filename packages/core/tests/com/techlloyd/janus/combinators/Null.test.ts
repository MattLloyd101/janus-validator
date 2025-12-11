import { Null } from '@/com/techlloyd/janus/combinators/Null';
import { DomainType, RNG, Generator } from '@/com/techlloyd/janus/index';

describe('Null', () => {
  describe('validation', () => {
    it('should validate null', () => {
      const validator = Null();
      expect(validator.validate(null).valid).toBe(true);
    });

    it('should reject undefined', () => {
      const validator = Null();
      const result = validator.validate(undefined);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('undefined');
      }
    });

    it('should reject falsy values that are not null', () => {
      const validator = Null();
      expect(validator.validate(0).valid).toBe(false);
      expect(validator.validate('').valid).toBe(false);
      expect(validator.validate(false).valid).toBe(false);
      expect(validator.validate(NaN).valid).toBe(false);
    });

    it('should reject truthy values', () => {
      const validator = Null();
      expect(validator.validate(1).valid).toBe(false);
      expect(validator.validate('null').valid).toBe(false);
      expect(validator.validate({}).valid).toBe(false);
      expect(validator.validate([]).valid).toBe(false);
    });

    it('should return null as the validated value', () => {
      const validator = Null();
      const result = validator.validate(null);
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe(null);
      }
    });
  });

  describe('domain', () => {
    it('should expose a FiniteDomain', () => {
      const validator = Null();
      expect(validator.domain.type).toBe(DomainType.FINITE_DOMAIN);
    });
  });

  describe('generation', () => {
    it('should generate null', () => {
      const validator = Null();
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);
      
      const value = generator.generate(validator);
      expect(value).toBe(null);
    });
  });
});

