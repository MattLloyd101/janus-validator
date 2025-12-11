import { Struct } from '@/com/techlloyd/janus/combinators/Struct';
import { Integer } from '@/com/techlloyd/janus/combinators/Integer';
import { UnicodeString } from '@/com/techlloyd/janus/combinators/UnicodeString';
import { Boolean } from '@/com/techlloyd/janus/combinators/Boolean';
import { Number } from '@/com/techlloyd/janus/combinators/Number';
import { DomainType, RNG, Generator } from '@/com/techlloyd/janus/index';

describe('Struct', () => {
  describe('validation', () => {
    it('should validate objects matching the schema', () => {
      const validator = Struct({
        name: UnicodeString(1, 100),
        age: Integer(0, 150),
        active: Boolean(),
      });

      const result = validator.validate({ name: 'Alice', age: 30, active: true });
      expect(result.valid).toBe(true);
    });

    it('should reject missing properties', () => {
      const validator = Struct({
        name: UnicodeString(),
        age: Integer(),
      });

      const result = validator.validate({ name: 'Alice' });
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('Missing required property');
        expect(result.error).toContain('age');
      }
    });

    it('should reject invalid property values', () => {
      const validator = Struct({
        name: UnicodeString(1, 10),
        age: Integer(0, 150),
      });

      const result = validator.validate({ name: 'Alice', age: 200 });
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain("Property 'age'");
      }
    });

    it('should allow extra properties in non-strict mode', () => {
      const validator = Struct({ name: UnicodeString() }, false);

      const result = validator.validate({ name: 'Alice', extra: 123 });
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toEqual({ name: 'Alice', extra: 123 });
      }
    });

    it('should reject extra properties in strict mode', () => {
      const validator = Struct({ name: UnicodeString() }, true);

      const result = validator.validate({ name: 'Alice', extra: 123 });
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('Unexpected properties');
        expect(result.error).toContain('extra');
      }
    });

    it('should reject null', () => {
      const validator = Struct({ name: UnicodeString() });

      const result = validator.validate(null);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('null');
      }
    });

    it('should reject arrays', () => {
      const validator = Struct({ name: UnicodeString() });

      const result = validator.validate(['Alice']);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('array');
      }
    });

    it('should reject primitives', () => {
      const validator = Struct({ name: UnicodeString() });

      expect(validator.validate('string').valid).toBe(false);
      expect(validator.validate(123).valid).toBe(false);
      expect(validator.validate(true).valid).toBe(false);
      expect(validator.validate(undefined).valid).toBe(false);
    });

    it('should validate nested objects', () => {
      const addressValidator = Struct({
        street: UnicodeString(),
        city: UnicodeString(),
        zip: UnicodeString(5, 10),
      });

      const userValidator = Struct({
        name: UnicodeString(),
        address: addressValidator,
      });

      const validUser = {
        name: 'Alice',
        address: {
          street: '123 Main St',
          city: 'Springfield',
          zip: '12345',
        },
      };

      expect(userValidator.validate(validUser).valid).toBe(true);

      const invalidUser = {
        name: 'Bob',
        address: {
          street: '456 Oak Ave',
          city: 'Shelbyville',
          zip: '1', // Too short
        },
      };

      const result = userValidator.validate(invalidUser);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain("Property 'address'");
      }
    });

    it('should return validated values', () => {
      const validator = Struct({
        count: Integer(0, 100),
        ratio: Number(0, 1),
      });

      const result = validator.validate({ count: 42, ratio: 0.5 });
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toEqual({ count: 42, ratio: 0.5 });
      }
    });

    it('should handle empty schema', () => {
      const validator = Struct({});

      expect(validator.validate({}).valid).toBe(true);
      expect(validator.validate({ any: 'thing' }).valid).toBe(true);

      const strictValidator = Struct({}, true);
      expect(strictValidator.validate({}).valid).toBe(true);
      expect(strictValidator.validate({ any: 'thing' }).valid).toBe(false);
    });
  });

  describe('domain', () => {
    it('should expose an ObjectDomain type', () => {
      const validator = Struct({
        name: UnicodeString(),
        age: Integer(),
      });

      expect(validator.domain.type).toBe(DomainType.STRUCT_DOMAIN);
    });

    it('should include schema domains', () => {
      const validator = Struct({
        name: UnicodeString(1, 50),
        age: Integer(0, 150),
      });

      const domain = validator.domain as any;
      expect(domain.schema.name).toBeDefined();
      expect(domain.schema.age).toBeDefined();
    });

    it('should include strict flag', () => {
      const nonStrict = Struct({ name: UnicodeString() }, false);
      const strict = Struct({ name: UnicodeString() }, true);

      expect((nonStrict.domain as any).strict).toBe(false);
      expect((strict.domain as any).strict).toBe(true);
    });
  });

  describe('generation', () => {
    it('should generate objects matching the schema', () => {
      const validator = Struct({
        name: UnicodeString(1, 20),
        age: Integer(0, 100),
        active: Boolean(),
      });

      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator) as any;
        
        expect(typeof value).toBe('object');
        expect(typeof value.name).toBe('string');
        expect(typeof value.age).toBe('number');
        expect(typeof value.active).toBe('boolean');
        
        expect(value.name.length).toBeGreaterThanOrEqual(1);
        expect(value.name.length).toBeLessThanOrEqual(20);
        expect(value.age).toBeGreaterThanOrEqual(0);
        expect(value.age).toBeLessThanOrEqual(100);
      }
    });

    it('should generate values that pass validation', () => {
      const validator = Struct({
        id: Integer(1, 1000),
        score: Number(0, 100),
        label: UnicodeString(1, 10),
      });

      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 100; i++) {
        const value = generator.generate(validator);
        const result = validator.validate(value);
        expect(result.valid).toBe(true);
      }
    });

    it('should generate nested objects', () => {
      const validator = Struct({
        user: Struct({
          name: UnicodeString(1, 20),
          email: UnicodeString(5, 50),
        }),
        count: Integer(0, 10),
      });

      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);
      const value = generator.generate(validator) as any;

      expect(typeof value.user).toBe('object');
      expect(typeof value.user.name).toBe('string');
      expect(typeof value.user.email).toBe('string');
      expect(typeof value.count).toBe('number');
    });
  });

  describe('strict mode edge cases', () => {
    it('should handle multiple extra properties', () => {
      const validator = Struct({ name: UnicodeString() }, true);

      const result = validator.validate({ 
        name: 'Alice', 
        extra1: 1, 
        extra2: 2, 
        extra3: 3 
      });
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('extra1');
      }
    });

    it('should pass strict validation when all properties match', () => {
      const validator = Struct({
        a: Integer(),
        b: UnicodeString(),
        c: Boolean(),
      }, true);

      expect(validator.validate({ a: 1, b: 'x', c: true }).valid).toBe(true);
    });
  });
});

