import { Constant } from '@/com/techlloyd/janus/combinators/Constant';
import { DomainType, RNG, Generator } from '@/com/techlloyd/janus/index';

describe('Constant', () => {
  describe('validation', () => {
    it('should validate exact value match', () => {
      const validator = Constant(42);
      expect(validator.validate(42).valid).toBe(true);
      expect(validator.validate(43).valid).toBe(false);
    });

    it('should work with strings', () => {
      const validator = Constant('hello');
      expect(validator.validate('hello').valid).toBe(true);
      expect(validator.validate('world').valid).toBe(false);
    });

    it('should work with booleans', () => {
      const trueValidator = Constant(true);
      expect(trueValidator.validate(true).valid).toBe(true);
      expect(trueValidator.validate(false).valid).toBe(false);

      const falseValidator = Constant(false);
      expect(falseValidator.validate(false).valid).toBe(true);
      expect(falseValidator.validate(true).valid).toBe(false);
    });

    it('should work with objects using reference equality', () => {
      const obj = { key: 'value' };
      const validator = Constant(obj);
      
      expect(validator.validate(obj).valid).toBe(true);
      expect(validator.validate({ key: 'value' }).valid).toBe(false); // Different reference
    });

    it('should support custom comparator', () => {
      // Deep equality for objects
      const validator = Constant(
        { x: 1, y: 2 },
        (input, val) => JSON.stringify(input) === JSON.stringify(val),
        'point'
      );
      
      expect(validator.validate({ x: 1, y: 2 }).valid).toBe(true);
      expect(validator.validate({ x: 1, y: 3 }).valid).toBe(false);
    });

    it('should support custom display name in errors', () => {
      const validator = Constant(42, undefined, 'the answer');
      const result = validator.validate(0);
      
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('the answer');
      }
    });

    it('should return the constant value on success', () => {
      const validator = Constant('test');
      const result = validator.validate('test');
      
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe('test');
      }
    });
  });

  describe('domain', () => {
    it('should expose a FiniteDomain with the constant value', () => {
      const validator = Constant(42);
      
      expect(validator.domain.type).toBe(DomainType.FINITE_DOMAIN);
      expect((validator.domain as any).values).toEqual([42]);
    });
  });

  describe('generation', () => {
    it('should always generate the constant value', () => {
      const validator = Constant('fixed');
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);
      
      for (let i = 0; i < 10; i++) {
        expect(generator.generate(validator.domain)).toBe('fixed');
      }
    });
  });

  describe('error formatting', () => {
    it('should format null correctly', () => {
      const validator = Constant(42);
      const result = validator.validate(null);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('null');
      }
    });

    it('should format undefined correctly', () => {
      const validator = Constant(42);
      const result = validator.validate(undefined);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('undefined');
      }
    });

    it('should format strings with quotes', () => {
      const validator = Constant(42);
      const result = validator.validate('hello');
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('"hello"');
      }
    });
  });
});

