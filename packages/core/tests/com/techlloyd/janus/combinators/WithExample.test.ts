import { withExample, validatorWithExample } from '@/com/techlloyd/janus/combinators/WithExample';
import { Integer } from '@/com/techlloyd/janus/combinators/Integer';
import { UnicodeString } from '@/com/techlloyd/janus/combinators/UnicodeString';
import { Boolean } from '@/com/techlloyd/janus/combinators/Boolean';
import { Struct } from '@/com/techlloyd/janus/combinators/Struct';
import { RNG } from '@/com/techlloyd/janus/index';

describe('withExample', () => {
  describe('validation with examples', () => {
    it('should include example when validation fails', () => {
      const validator = withExample(Integer(0, 100));
      
      const result = validator.validate('not a number');
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toBeDefined();
        expect(result.example).toBeDefined();
        expect(typeof result.example).toBe('number');
        expect(result.example).toBeGreaterThanOrEqual(0);
        expect(result.example).toBeLessThanOrEqual(100);
      }
    });

    it('should not include example when validation succeeds', () => {
      const validator = withExample(Integer(0, 100));
      
      const result = validator.validate(50);
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe(50);
        expect((result as any).example).toBeUndefined();
      }
    });

    it('should work with String validator', () => {
      const validator = withExample(UnicodeString(5, 10));
      
      const result = validator.validate(123);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.example).toBeDefined();
        expect(typeof result.example).toBe('string');
        expect(result.example!.length).toBeGreaterThanOrEqual(5);
        expect(result.example!.length).toBeLessThanOrEqual(10);
      }
    });

    it('should work with Boolean validator', () => {
      const validator = withExample(Boolean());
      
      const result = validator.validate('true');
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.example).toBeDefined();
        expect(typeof result.example).toBe('boolean');
      }
    });

    it('should work with Struct validator', () => {
      const validator = withExample(Struct({
        name: UnicodeString(1, 20),
        age: Integer(0, 100),
      }));
      
      const result = validator.validate({ name: 123, age: 'not a number' });
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.example).toBeDefined();
        expect(typeof result.example).toBe('object');
        expect(typeof (result.example as any).name).toBe('string');
        expect(typeof (result.example as any).age).toBe('number');
      }
    });

    it('should use custom RNG', () => {
      // Fixed RNG for deterministic testing
      const fixedRng: RNG = { random: () => 0.5 };
      const validator = withExample(Integer(0, 100), fixedRng);
      
      const result1 = validator.validate('invalid');
      const result2 = validator.validate('invalid');
      
      expect(result1.valid).toBe(false);
      expect(result2.valid).toBe(false);
      if (!result1.valid && !result2.valid) {
        // Same RNG value should produce same example
        expect(result1.example).toBe(result2.example);
      }
    });

    it('should preserve original error message', () => {
      const validator = withExample(Integer(0, 100));
      const baseValidator = Integer(0, 100);
      
      const resultWithExample = validator.validate('invalid');
      const resultWithoutExample = baseValidator.validate('invalid');
      
      expect(resultWithExample.valid).toBe(false);
      expect(resultWithoutExample.valid).toBe(false);
      if (!resultWithExample.valid && !resultWithoutExample.valid) {
        expect(resultWithExample.error).toBe(resultWithoutExample.error);
      }
    });

    it('should preserve domain', () => {
      const baseValidator = Integer(0, 100);
      const wrappedValidator = withExample(baseValidator);
      
      expect(wrappedValidator.domain).toBe(baseValidator.domain);
    });
  });

  describe('validatorWithExample factory', () => {
    it('should create wrapped validators', () => {
      const IntegerWithExample = validatorWithExample(Integer);
      const validator = IntegerWithExample(0, 100);
      
      const result = validator.validate('invalid');
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.example).toBeDefined();
        expect(typeof result.example).toBe('number');
      }
    });

    it('should pass arguments to underlying validator', () => {
      const StringWithExample = validatorWithExample(UnicodeString);
      const validator = StringWithExample(5, 10);
      
      const result = validator.validate(123);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.example).toBeDefined();
        expect(result.example!.length).toBeGreaterThanOrEqual(5);
        expect(result.example!.length).toBeLessThanOrEqual(10);
      }
    });
  });

  describe('example formatting', () => {
    it('should produce valid examples that pass validation', () => {
      const validator = withExample(Integer(10, 20));
      
      const result = validator.validate('invalid');
      expect(result.valid).toBe(false);
      if (!result.valid && result.example !== undefined) {
        // The example should pass validation
        const exampleResult = validator.validate(result.example);
        expect(exampleResult.valid).toBe(true);
      }
    });

    it('should produce varied examples with random RNG', () => {
      const validator = withExample(Integer(0, 1000000));
      const examples = new Set<number>();
      
      for (let i = 0; i < 20; i++) {
        const result = validator.validate('invalid');
        if (!result.valid && result.example !== undefined) {
          examples.add(result.example);
        }
      }
      
      // Should have multiple different examples
      expect(examples.size).toBeGreaterThan(1);
    });
  });
});

