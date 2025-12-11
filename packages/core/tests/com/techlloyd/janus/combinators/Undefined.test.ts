import { Undefined } from '@/com/techlloyd/janus/combinators/Undefined';
import { DomainType, RNG, Generator } from '@/com/techlloyd/janus/index';

describe('Undefined', () => {
  describe('validation', () => {
    it('should validate undefined', () => {
      const validator = Undefined();
      expect(validator.validate(undefined).valid).toBe(true);
    });

    it('should validate void 0', () => {
      const validator = Undefined();
      expect(validator.validate(void 0).valid).toBe(true);
    });

    it('should reject null', () => {
      const validator = Undefined();
      const result = validator.validate(null);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('null');
      }
    });

    it('should reject falsy values that are not undefined', () => {
      const validator = Undefined();
      expect(validator.validate(0).valid).toBe(false);
      expect(validator.validate('').valid).toBe(false);
      expect(validator.validate(false).valid).toBe(false);
      expect(validator.validate(NaN).valid).toBe(false);
    });

    it('should reject truthy values', () => {
      const validator = Undefined();
      expect(validator.validate(1).valid).toBe(false);
      expect(validator.validate('undefined').valid).toBe(false);
      expect(validator.validate({}).valid).toBe(false);
      expect(validator.validate([]).valid).toBe(false);
    });

    it('should return undefined as the validated value', () => {
      const validator = Undefined();
      const result = validator.validate(undefined);
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe(undefined);
      }
    });
  });

  describe('domain', () => {
    it('should expose a FiniteDomain', () => {
      const validator = Undefined();
      expect(validator.domain.type).toBe(DomainType.FINITE_DOMAIN);
    });
  });

  describe('generation', () => {
    it('should generate undefined', () => {
      const validator = Undefined();
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);
      
      const value = generator.generate(validator);
      expect(value).toBe(undefined);
    });
  });
});

