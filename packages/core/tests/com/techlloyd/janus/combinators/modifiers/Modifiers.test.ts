import { UnicodeString } from '@/com/techlloyd/janus/combinators/UnicodeString';
import { Integer } from '@/com/techlloyd/janus/combinators/Integer';
import { Boolean as BooleanValidator } from '@/com/techlloyd/janus/combinators/Boolean';
import { Struct } from '@/com/techlloyd/janus/combinators/Struct';
import { Generator } from '@/com/techlloyd/janus/Generator';
import {
  optional,
  nullable,
  nullish,
  withDefault,
  OptionalValidator,
  NullableValidator,
  NullishValidator,
  DefaultValidator,
} from '@/com/techlloyd/janus/combinators/modifiers';

describe('Modifiers', () => {
  describe('optional()', () => {
    describe('standalone function', () => {
      it('should accept the inner type', () => {
        const validator = optional(UnicodeString(1, 50));
        const result = validator.validate('hello');
        expect(result.valid).toBe(true);
        if (result.valid) {
          expect(result.value).toBe('hello');
        }
      });

      it('should accept undefined', () => {
        const validator = optional(Integer(0, 100));
        const result = validator.validate(undefined);
        expect(result.valid).toBe(true);
        if (result.valid) {
          expect(result.value).toBe(undefined);
        }
      });

      it('should reject null', () => {
        const validator = optional(UnicodeString(1, 50));
        const result = validator.validate(null);
        expect(result.valid).toBe(false);
      });

      it('should reject invalid values', () => {
        const validator = optional(Integer(0, 100));
        expect(validator.validate(150).valid).toBe(false);
        expect(validator.validate('not a number').valid).toBe(false);
      });
    });

    describe('fluent method .optional()', () => {
      it('should work on string validators', () => {
        const validator = UnicodeString(1, 50).optional();
        expect(validator.validate('hello').valid).toBe(true);
        expect(validator.validate(undefined).valid).toBe(true);
        expect(validator.validate(null).valid).toBe(false);
      });

      it('should work on integer validators', () => {
        const validator = Integer(0, 100).optional();
        expect(validator.validate(50).valid).toBe(true);
        expect(validator.validate(undefined).valid).toBe(true);
        expect(validator.validate(150).valid).toBe(false);
      });

      it('should work on boolean validators', () => {
        const validator = BooleanValidator().optional();
        expect(validator.validate(true).valid).toBe(true);
        expect(validator.validate(false).valid).toBe(true);
        expect(validator.validate(undefined).valid).toBe(true);
        expect(validator.validate('true').valid).toBe(false);
      });
    });

    describe('generation', () => {
      it('should generate valid values from domain', () => {
        const validator = optional(Integer(0, 100));
        const generator = new Generator({ random: Math.random });
        
        for (let i = 0; i < 20; i++) {
          const value = generator.generate(validator.domain);
          const result = validator.validate(value);
          expect(result.valid).toBe(true);
        }
      });

      it('should sometimes generate undefined', () => {
        const validator = optional(Integer(0, 100));
        const generator = new Generator({ random: Math.random });
        
        let hasUndefined = false;
        let hasNumber = false;
        
        for (let i = 0; i < 50; i++) {
          const value = generator.generate(validator.domain);
          if (value === undefined) hasUndefined = true;
          if (typeof value === 'number') hasNumber = true;
        }
        
        // Should generate both undefined and numbers
        expect(hasUndefined || hasNumber).toBe(true);
      });
    });
  });

  describe('nullable()', () => {
    describe('standalone function', () => {
      it('should accept the inner type', () => {
        const validator = nullable(UnicodeString(1, 50));
        const result = validator.validate('hello');
        expect(result.valid).toBe(true);
        if (result.valid) {
          expect(result.value).toBe('hello');
        }
      });

      it('should accept null', () => {
        const validator = nullable(Integer(0, 100));
        const result = validator.validate(null);
        expect(result.valid).toBe(true);
        if (result.valid) {
          expect(result.value).toBe(null);
        }
      });

      it('should reject undefined', () => {
        const validator = nullable(UnicodeString(1, 50));
        const result = validator.validate(undefined);
        expect(result.valid).toBe(false);
      });

      it('should reject invalid values', () => {
        const validator = nullable(Integer(0, 100));
        expect(validator.validate(150).valid).toBe(false);
        expect(validator.validate('not a number').valid).toBe(false);
      });
    });

    describe('fluent method .nullable()', () => {
      it('should work on string validators', () => {
        const validator = UnicodeString(1, 50).nullable();
        expect(validator.validate('hello').valid).toBe(true);
        expect(validator.validate(null).valid).toBe(true);
        expect(validator.validate(undefined).valid).toBe(false);
      });

      it('should work on integer validators', () => {
        const validator = Integer(0, 100).nullable();
        expect(validator.validate(50).valid).toBe(true);
        expect(validator.validate(null).valid).toBe(true);
        expect(validator.validate(undefined).valid).toBe(false);
      });
    });

    describe('generation', () => {
      it('should generate valid values from domain', () => {
        const validator = nullable(Integer(0, 100));
        const generator = new Generator({ random: Math.random });
        
        for (let i = 0; i < 20; i++) {
          const value = generator.generate(validator.domain);
          const result = validator.validate(value);
          expect(result.valid).toBe(true);
        }
      });
    });
  });

  describe('nullish()', () => {
    describe('standalone function', () => {
      it('should accept the inner type', () => {
        const validator = nullish(UnicodeString(1, 50));
        const result = validator.validate('hello');
        expect(result.valid).toBe(true);
        if (result.valid) {
          expect(result.value).toBe('hello');
        }
      });

      it('should accept null', () => {
        const validator = nullish(Integer(0, 100));
        const result = validator.validate(null);
        expect(result.valid).toBe(true);
        if (result.valid) {
          expect(result.value).toBe(null);
        }
      });

      it('should accept undefined', () => {
        const validator = nullish(Integer(0, 100));
        const result = validator.validate(undefined);
        expect(result.valid).toBe(true);
        if (result.valid) {
          expect(result.value).toBe(undefined);
        }
      });

      it('should reject invalid values', () => {
        const validator = nullish(Integer(0, 100));
        expect(validator.validate(150).valid).toBe(false);
        expect(validator.validate('not a number').valid).toBe(false);
      });
    });

    describe('fluent method .nullish()', () => {
      it('should work on string validators', () => {
        const validator = UnicodeString(1, 50).nullish();
        expect(validator.validate('hello').valid).toBe(true);
        expect(validator.validate(null).valid).toBe(true);
        expect(validator.validate(undefined).valid).toBe(true);
        expect(validator.validate(123).valid).toBe(false);
      });
    });

    describe('generation', () => {
      it('should generate valid values from domain', () => {
        const validator = nullish(Integer(0, 100));
        const generator = new Generator({ random: Math.random });
        
        for (let i = 0; i < 20; i++) {
          const value = generator.generate(validator.domain);
          const result = validator.validate(value);
          expect(result.valid).toBe(true);
        }
      });
    });
  });

  describe('withDefault()', () => {
    describe('standalone function', () => {
      it('should return the validated value when not undefined', () => {
        const validator = withDefault(Integer(0, 100), 42);
        const result = validator.validate(75);
        expect(result.valid).toBe(true);
        if (result.valid) {
          expect(result.value).toBe(75);
        }
      });

      it('should return the default value when undefined', () => {
        const validator = withDefault(Integer(0, 100), 42);
        const result = validator.validate(undefined);
        expect(result.valid).toBe(true);
        if (result.valid) {
          expect(result.value).toBe(42);
        }
      });

      it('should reject null (null is not undefined)', () => {
        const validator = withDefault(Integer(0, 100), 42);
        const result = validator.validate(null);
        expect(result.valid).toBe(false);
      });

      it('should reject invalid values', () => {
        const validator = withDefault(Integer(0, 100), 42);
        expect(validator.validate(150).valid).toBe(false);
        expect(validator.validate('not a number').valid).toBe(false);
      });

      it('should support factory function for dynamic defaults', () => {
        let callCount = 0;
        const validator = withDefault(Integer(0, 1000), () => {
          callCount++;
          return callCount * 10;
        });

        const result1 = validator.validate(undefined);
        expect(result1.valid).toBe(true);
        if (result1.valid) {
          expect(result1.value).toBe(10);
        }

        const result2 = validator.validate(undefined);
        expect(result2.valid).toBe(true);
        if (result2.valid) {
          expect(result2.value).toBe(20);
        }
      });

      it('should not call factory when value is provided', () => {
        let called = false;
        const validator = withDefault(Integer(0, 100), () => {
          called = true;
          return 42;
        });

        validator.validate(50);
        expect(called).toBe(false);
      });
    });

    describe('fluent method .default()', () => {
      it('should work with static default', () => {
        const validator = Integer(0, 100).default(42);
        
        const result1 = validator.validate(75);
        expect(result1.valid).toBe(true);
        if (result1.valid) expect(result1.value).toBe(75);

        const result2 = validator.validate(undefined);
        expect(result2.valid).toBe(true);
        if (result2.valid) expect(result2.value).toBe(42);
      });

      it('should work with factory default', () => {
        const validator = Integer(0, 100).default(() => 42);
        const result = validator.validate(undefined);
        expect(result.valid).toBe(true);
        if (result.valid) expect(result.value).toBe(42);
      });

      it('should work on string validators', () => {
        const validator = UnicodeString(1, 50).default('default');
        
        const result1 = validator.validate('hello');
        expect(result1.valid).toBe(true);
        if (result1.valid) expect(result1.value).toBe('hello');

        const result2 = validator.validate(undefined);
        expect(result2.valid).toBe(true);
        if (result2.valid) expect(result2.value).toBe('default');
      });

      it('should work on boolean validators', () => {
        const validator = BooleanValidator().default(false);
        
        expect(validator.validate(true).valid).toBe(true);
        
        const result = validator.validate(undefined);
        expect(result.valid).toBe(true);
        if (result.valid) expect(result.value).toBe(false);
      });
    });

    describe('generation', () => {
      it('should use inner domain for generation', () => {
        const validator = withDefault(Integer(10, 20), 15);
        const generator = new Generator({ random: Math.random });
        
        for (let i = 0; i < 20; i++) {
          const value = generator.generate(validator.domain);
          expect(typeof value).toBe('number');
          expect(value).toBeGreaterThanOrEqual(10);
          expect(value).toBeLessThanOrEqual(20);
        }
      });
    });
  });

  describe('chaining modifiers', () => {
    it('should allow chaining optional and default', () => {
      // optional().default() - if undefined, use default, otherwise validate
      // This creates: OptionalValidator -> DefaultValidator
      const validator = Integer(0, 100).optional();
      
      expect(validator.validate(50).valid).toBe(true);
      expect(validator.validate(undefined).valid).toBe(true);
    });

    it('should work in struct schemas', () => {
      const schema = Struct({
        name: UnicodeString(1, 50),
        age: Integer(0, 150).optional(),
        count: Integer(0, 100).default(0),
      });

      // All fields provided
      const result1 = schema.validate({ name: 'Alice', age: 30, count: 5 });
      expect(result1.valid).toBe(true);

      // Optional field missing (undefined)
      const result2 = schema.validate({ name: 'Bob', count: 10 });
      expect(result2.valid).toBe(true);

      // Default field missing (undefined)
      const result3 = schema.validate({ name: 'Charlie', age: 25 });
      expect(result3.valid).toBe(true);
      if (result3.valid) {
        expect(result3.value.count).toBe(0);
      }
    });
  });

  describe('type inference', () => {
    it('optional should produce T | undefined', () => {
      const validator = optional(Integer(0, 100));
      const result = validator.validate(42);
      
      if (result.valid) {
        // TypeScript should infer result.value as number | undefined
        const value: number | undefined = result.value;
        expect(value).toBe(42);
      }
    });

    it('nullable should produce T | null', () => {
      const validator = nullable(Integer(0, 100));
      const result = validator.validate(null);
      
      if (result.valid) {
        // TypeScript should infer result.value as number | null
        const value: number | null = result.value;
        expect(value).toBe(null);
      }
    });

    it('nullish should produce T | null | undefined', () => {
      const validator = nullish(Integer(0, 100));
      const result = validator.validate(undefined);
      
      if (result.valid) {
        // TypeScript should infer result.value as number | null | undefined
        const value: number | null | undefined = result.value;
        expect(value).toBe(undefined);
      }
    });

    it('withDefault should preserve the original type', () => {
      const validator = withDefault(Integer(0, 100), 42);
      const result = validator.validate(undefined);
      
      if (result.valid) {
        // TypeScript should infer result.value as number (not number | undefined)
        const value: number = result.value;
        expect(value).toBe(42);
      }
    });
  });
});
