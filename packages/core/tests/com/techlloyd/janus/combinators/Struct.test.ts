import { Struct } from '@/com/techlloyd/janus/combinators/Struct';
import { Integer } from '@/com/techlloyd/janus/combinators/Integer';
import { UnicodeString } from '@/com/techlloyd/janus/combinators/UnicodeString';
import { Boolean } from '@/com/techlloyd/janus/combinators/Boolean';
import { Float } from '@/com/techlloyd/janus/combinators/Float';
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
        expect(result.error).toContain('age');
        // Structured errors preserve the property path
        expect(result.results).toHaveProperty('age');
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
        expect(result.error).toContain('extra');
        expect(result.error).toContain('Unexpected property');
        // Structured errors preserve the property
        expect(result.results).toHaveProperty('extra');
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
        expect(result.error).toContain('address');
        expect(result.error).toContain('zip');
        // Structured errors preserve nested paths
        expect(result.results).toHaveProperty('address');
      }
    });

    it('should return validated values', () => {
      const validator = Struct({
        count: Integer(0, 100),
        ratio: Float(0, 1),
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

    it('should collect all errors in structured format', () => {
      const validator = Struct({
        name: UnicodeString(1, 50),
        age: Integer(0, 150),
        email: UnicodeString(5, 100),
      });

      // Multiple fields failing
      const result = validator.validate({
        name: '', // too short
        age: 200, // too high
        email: 'x', // too short
      });

      expect(result.valid).toBe(false);
      if (!result.valid) {
        // Structured results contain per-field ValidationResults
        const results = result.results as Record<string, { valid: boolean; error?: string; value?: any }>;
        expect(results).toHaveProperty('name');
        expect(results).toHaveProperty('age');
        expect(results).toHaveProperty('email');
        
        // Each result is a ValidationResult object
        expect(results.name.valid).toBe(false);
        expect(results.age.valid).toBe(false);
        expect(results.email.valid).toBe(false);
        expect(results.name.error).toMatch(/>=\s*1|less than minimum/);
        expect(results.age.error).toMatch(/<=\s*150|greater than maximum/);
      }
    });

    it('should provide nested structured errors', () => {
      const addressValidator = Struct({
        city: UnicodeString(1, 50),
        zip: UnicodeString(5, 5),
      });
      
      const userValidator = Struct({
        name: UnicodeString(1, 50),
        address: addressValidator,
      });

      const result = userValidator.validate({
        name: 'Alice',
        address: {
          city: '', // too short
          zip: '1', // too short
        },
      });

      expect(result.valid).toBe(false);
      if (!result.valid) {
        // Nested structure preserved - results contain ValidationResults
        const results = result.results as Record<string, any>;
        
        // name passed
        expect(results.name.valid).toBe(true);
        expect(results.name.value).toBe('Alice');
        
        // address failed with nested results
        expect(results.address.valid).toBe(false);
        expect(results.address.results).toBeDefined();
        expect(results.address.results.city.valid).toBe(false);
        expect(results.address.results.zip.valid).toBe(false);
        
        // Flattened error contains full path
        expect(result.error).toContain('address.city');
        expect(result.error).toContain('address.zip');
      }
    });
  });

  describe('domain', () => {
    it('should expose an ObjectDomain type', () => {
      const validator = Struct({
        name: UnicodeString(),
        age: Integer(),
      });

      expect(validator.domain.kind).toBe(DomainType.STRUCT);
    });

    it('should include schema domains', () => {
      const validator = Struct({
        name: UnicodeString(1, 50),
        age: Integer(0, 150),
      });

      expect(validator.domain.fields.name).toBeDefined();
      expect(validator.domain.fields.age).toBeDefined();
    });

    it('should include strict flag', () => {
      const nonStrict = Struct({ name: UnicodeString() }, false);
      const strict = Struct({ name: UnicodeString() }, true);

      expect(nonStrict.domain.strict).toBe(false);
      expect(strict.domain.strict).toBe(true);
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
        const value = generator.generate(validator.domain);
        
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
        score: Float(0, 100),
        label: UnicodeString(1, 10),
      });

      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 100; i++) {
        const value = generator.generate(validator.domain);
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
      const value = generator.generate(validator.domain);

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

