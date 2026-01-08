import { UnicodeString } from '@/com/techlloyd/janus/combinators/UnicodeString';
import { Integer } from '@/com/techlloyd/janus/combinators/Integer';
import { Struct } from '@/com/techlloyd/janus/combinators/Struct';
import { Generator } from '@/com/techlloyd/janus/Generator';
import {
  transform,
  TransformValidator,
} from '@/com/techlloyd/janus/combinators/modifiers';

describe('Transform', () => {
  describe('standalone transform() function', () => {
    it('should transform string to trimmed string', () => {
      const validator = transform(UnicodeString(1, 100), s => s.trim());
      const result = validator.validate('  hello  ');
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe('hello');
      }
    });

    it('should transform string to lowercase', () => {
      const validator = transform(UnicodeString(1, 100), s => s.toLowerCase());
      const result = validator.validate('HELLO');
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe('hello');
      }
    });

    it('should transform string to uppercase', () => {
      const validator = transform(UnicodeString(1, 100), s => s.toUpperCase());
      const result = validator.validate('hello');
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe('HELLO');
      }
    });

    it('should transform string to number (type change)', () => {
      const validator = transform(UnicodeString(), s => parseInt(s, 10));
      const result = validator.validate('42');
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe(42);
        expect(typeof result.value).toBe('number');
      }
    });

    it('should pass through inner validation errors', () => {
      const validator = transform(UnicodeString(5, 10), s => s.trim());
      const result = validator.validate('hi'); // too short
      expect(result.valid).toBe(false);
    });

    it('should handle transform errors gracefully', () => {
      const validator = transform(UnicodeString(), s => JSON.parse(s));
      const result = validator.validate('not valid json');
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('Transform failed');
      }
    });

    it('should use custom error message when provided', () => {
      const validator = transform(
        UnicodeString(),
        s => {
          const d = new Date(s);
          if (isNaN(d.getTime())) throw new Error('bad date');
          return d;
        },
        'Please provide a valid date'
      );
      const result = validator.validate('not a date');
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toBe('Please provide a valid date');
      }
    });

    it('should chain transforms via nested transform calls', () => {
      // Chain transforms using nested transform() calls
      const inner = transform(UnicodeString(1, 100), s => s.trim());
      const validator = transform(inner, s => s.toLowerCase());
      
      const result = validator.validate('  HELLO  ');
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe('hello');
      }
    });
  });

  describe('fluent .transform() method', () => {
    it('should work with basic transform', () => {
      const validator = UnicodeString(1, 100).transform(s => s.trim());
      const result = validator.validate('  hello  ');
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe('hello');
      }
    });

    it('should work on integer validators', () => {
      const validator = Integer(0, 100).transform(n => n * 2);
      const result = validator.validate(21);
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe(42);
      }
    });

    it('should chain multiple transforms fluently', () => {
      // This tests the fluent chaining - each method should return a TransformValidator
      // that has the same methods available
      const validator = UnicodeString(1, 100)
        .trim()
        .toLowerCase()
        .transform(s => s.replace(/\s+/g, '-'));

      const result = validator.validate('  Hello World  ');
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe('hello-world');
      }
    });

    it('should chain trim and toLowerCase', () => {
      const validator = UnicodeString(1, 100).trim().toLowerCase();
      const result = validator.validate('  HELLO  ');
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe('hello');
      }
    });

    it('should chain toUpperCase after trim', () => {
      const validator = UnicodeString(1, 100).trim().toUpperCase();
      const result = validator.validate('  hello  ');
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe('HELLO');
      }
    });

    it('should chain transform after toLowerCase', () => {
      const validator = UnicodeString(1, 100)
        .toLowerCase()
        .transform(s => `prefix_${s}`);
      
      const result = validator.validate('HELLO');
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe('prefix_hello');
      }
    });

    it('should chain optional after transform', () => {
      const validator = UnicodeString(1, 100)
        .trim()
        .toLowerCase()
        .optional();
      
      expect(validator.validate('  HELLO  ')).toEqual({ valid: true, value: 'hello' });
      expect(validator.validate(undefined)).toEqual({ valid: true, value: undefined });
    });

    it('should chain default after transform', () => {
      const validator = UnicodeString(1, 100)
        .trim()
        .toLowerCase()
        .default('default');
      
      expect(validator.validate('  HELLO  ')).toEqual({ valid: true, value: 'hello' });
      expect(validator.validate(undefined)).toEqual({ valid: true, value: 'default' });
    });
  });

  describe('convenience string methods', () => {
    describe('.trim()', () => {
      it('should trim whitespace from string', () => {
        const validator = UnicodeString(1, 100).trim();
        const result = validator.validate('  hello  ');
        expect(result.valid).toBe(true);
        if (result.valid) {
          expect(result.value).toBe('hello');
        }
      });

      it('should handle strings with only whitespace after trim', () => {
        const validator = UnicodeString(0, 100).trim();
        const result = validator.validate('   ');
        expect(result.valid).toBe(true);
        if (result.valid) {
          expect(result.value).toBe('');
        }
      });
    });

    describe('.toLowerCase()', () => {
      it('should convert string to lowercase', () => {
        const validator = UnicodeString(1, 100).toLowerCase();
        const result = validator.validate('HeLLo WoRLD');
        expect(result.valid).toBe(true);
        if (result.valid) {
          expect(result.value).toBe('hello world');
        }
      });
    });

    describe('.toUpperCase()', () => {
      it('should convert string to uppercase', () => {
        const validator = UnicodeString(1, 100).toUpperCase();
        const result = validator.validate('hello world');
        expect(result.valid).toBe(true);
        if (result.valid) {
          expect(result.value).toBe('HELLO WORLD');
        }
      });
    });
  });

  describe('in struct schemas', () => {
    it('should transform fields in struct', () => {
      const schema = Struct({
        name: UnicodeString(1, 100).trim(),
        email: transform(
          UnicodeString(5, 100).trim(),
          s => s.toLowerCase()
        ),
      });

      const result = schema.validate({
        name: '  Alice Smith  ',
        email: '  ALICE@EXAMPLE.COM  ',
      });

      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value.name).toBe('Alice Smith');
        expect(result.value.email).toBe('alice@example.com');
      }
    });
  });

  describe('domain and generation', () => {
    it('should have a TransformDomain', () => {
      const validator = UnicodeString(1, 50).transform(s => s.toUpperCase());
      expect(validator.domain).toBeDefined();
      expect(validator.domain.kind).toBe('transform');
    });

    it('should generate valid values and transform them', () => {
      const validator = UnicodeString(1, 50).toUpperCase();
      const generator = new Generator({ random: Math.random });

      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator.domain);
        expect(typeof value).toBe('string');
        // Generated values should be uppercase
        expect(value).toBe((value as string).toUpperCase());
      }
    });

    it('should generate then transform for type-changing transforms', () => {
      const validator = UnicodeString(1, 5).transform(s => s.length);
      const generator = new Generator({ random: Math.random });

      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator.domain);
        expect(typeof value).toBe('number');
        expect(value).toBeGreaterThanOrEqual(1);
        expect(value).toBeLessThanOrEqual(5);
      }
    });
  });

  describe('type inference', () => {
    it('transform should change the output type', () => {
      const validator = UnicodeString().transform(s => parseInt(s, 10));
      const result = validator.validate('42');

      if (result.valid) {
        // TypeScript should infer result.value as number
        const value: number = result.value;
        expect(value).toBe(42);
      }
    });

    it('trim should preserve string type', () => {
      const validator = UnicodeString(1, 100).trim();
      const result = validator.validate('  HELLO  ');

      if (result.valid) {
        // TypeScript should infer result.value as string
        const value: string = result.value;
        expect(value).toBe('HELLO');
      }
    });
  });

  describe('edge cases', () => {
    it('should handle empty string after trim', () => {
      const validator = UnicodeString(0, 100).trim();
      const result = validator.validate('   ');
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe('');
      }
    });

    it('should handle identity transform', () => {
      const validator = UnicodeString(1, 100).transform(s => s);
      const result = validator.validate('hello');
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe('hello');
      }
    });

    it('should handle transform that returns null', () => {
      const validator = UnicodeString(1, 100).transform(() => null);
      const result = validator.validate('hello');
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe(null);
      }
    });

    it('should handle transform that returns undefined', () => {
      const validator = UnicodeString(1, 100).transform(() => undefined);
      const result = validator.validate('hello');
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe(undefined);
      }
    });

    it('should handle transform that returns object', () => {
      const validator = UnicodeString(1, 100).transform(s => ({ length: s.length, original: s }));
      const result = validator.validate('hello');
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toEqual({ length: 5, original: 'hello' });
      }
    });

    it('should handle transform that returns array', () => {
      const validator = UnicodeString(1, 100).transform(s => s.split(''));
      const result = validator.validate('hi');
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toEqual(['h', 'i']);
      }
    });
  });

  describe('real-world examples', () => {
    it('should normalize email addresses', () => {
      const emailValidator = transform(
        UnicodeString(5, 100).trim(),
        s => s.toLowerCase()
      );

      const result = emailValidator.validate('  Alice@Example.COM  ');
      expect(result).toEqual({
        valid: true,
        value: 'alice@example.com',
      });
    });

    it('should parse JSON configuration', () => {
      const configValidator = UnicodeString()
        .transform(s => JSON.parse(s) as { port: number; host: string });

      const result = configValidator.validate('{"port": 3000, "host": "localhost"}');
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toEqual({ port: 3000, host: 'localhost' });
      }
    });

    it('should coerce string to number', () => {
      const numberValidator = transform(
        UnicodeString().trim(),
        s => {
          const n = Number(s);
          if (isNaN(n)) throw new Error('Not a number');
          return n;
        }
      );

      expect(numberValidator.validate('  42  ')).toEqual({ valid: true, value: 42 });
      expect(numberValidator.validate('  3.14  ')).toEqual({ valid: true, value: 3.14 });

      const invalidResult = numberValidator.validate('not a number');
      expect(invalidResult.valid).toBe(false);
    });
  });
});
