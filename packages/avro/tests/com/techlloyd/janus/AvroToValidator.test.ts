import { avroToValidator } from '../../../../src/com/techlloyd/janus/AvroToValidator';
import { Generator, RNG } from '@janus-validator/core';
import type { AvroRecordType, AvroEnumType, AvroArrayType } from '../../../../src/com/techlloyd/janus/types';

describe('avroToValidator', () => {
  // Helper to create a seeded RNG for deterministic tests
  const createRng = (): RNG => {
    let seed = 12345;
    return {
      random: () => {
        seed = (seed * 1103515245 + 12345) & 0x7fffffff;
        return seed / 0x7fffffff;
      },
    };
  };

  describe('primitive types', () => {
    it('converts null type', () => {
      const validator = avroToValidator('null');
      expect(validator.validate(null).valid).toBe(true);
      expect(validator.validate('string').valid).toBe(false);
    });

    it('converts boolean type', () => {
      const validator = avroToValidator('boolean');
      expect(validator.validate(true).valid).toBe(true);
      expect(validator.validate(false).valid).toBe(true);
      expect(validator.validate('true').valid).toBe(false);
    });

    it('converts int type', () => {
      const validator = avroToValidator('int');
      expect(validator.validate(42).valid).toBe(true);
      expect(validator.validate(-100).valid).toBe(true);
      expect(validator.validate(3.14).valid).toBe(false);
      expect(validator.validate('42').valid).toBe(false);
    });

    it('converts int type with min/max constraints', () => {
      const schema = {
        type: 'record',
        name: 'Test',
        fields: [
          { name: 'age', type: 'int', 'x-janus-min': 0, 'x-janus-max': 150 },
        ],
      } as AvroRecordType;

      const validator = avroToValidator(schema);
      expect(validator.validate({ age: 25 }).valid).toBe(true);
      expect(validator.validate({ age: 0 }).valid).toBe(true);
      expect(validator.validate({ age: 150 }).valid).toBe(true);
      expect(validator.validate({ age: -1 }).valid).toBe(false);
      expect(validator.validate({ age: 151 }).valid).toBe(false);
    });

    it('converts long type', () => {
      const validator = avroToValidator('long');
      expect(validator.validate(9007199254740991n).valid).toBe(true);
      expect(validator.validate(-9007199254740991n).valid).toBe(true);
    });

    it('converts float type', () => {
      const validator = avroToValidator('float');
      expect(validator.validate(3.14).valid).toBe(true);
      expect(validator.validate(-2.5).valid).toBe(true);
      expect(validator.validate('3.14').valid).toBe(false);
    });

    it('converts double type', () => {
      const validator = avroToValidator('double');
      expect(validator.validate(3.14159265359).valid).toBe(true);
    });

    it('converts double type with min/max constraints', () => {
      const schema = {
        type: 'record',
        name: 'Test',
        fields: [
          { name: 'percent', type: 'double', 'x-janus-min': 0, 'x-janus-max': 100 },
        ],
      } as AvroRecordType;

      const validator = avroToValidator(schema);
      expect(validator.validate({ percent: 50.5 }).valid).toBe(true);
      expect(validator.validate({ percent: 0 }).valid).toBe(true);
      expect(validator.validate({ percent: 100 }).valid).toBe(true);
      expect(validator.validate({ percent: -0.1 }).valid).toBe(false);
      expect(validator.validate({ percent: 100.1 }).valid).toBe(false);
    });

    it('converts string type', () => {
      const validator = avroToValidator('string');
      expect(validator.validate('hello').valid).toBe(true);
      expect(validator.validate('').valid).toBe(true);
      expect(validator.validate(123).valid).toBe(false);
    });

    it('converts string type with length constraints', () => {
      const schema = {
        type: 'record',
        name: 'Test',
        fields: [
          { name: 'name', type: 'string', 'x-janus-minLength': 1, 'x-janus-maxLength': 10 },
        ],
      } as AvroRecordType;

      const validator = avroToValidator(schema);
      expect(validator.validate({ name: 'Alice' }).valid).toBe(true);
      expect(validator.validate({ name: 'A' }).valid).toBe(true);
      expect(validator.validate({ name: '1234567890' }).valid).toBe(true);
      expect(validator.validate({ name: '' }).valid).toBe(false);
      expect(validator.validate({ name: '12345678901' }).valid).toBe(false);
    });

    it('converts string type with pattern constraint', () => {
      const schema = {
        type: 'record',
        name: 'Test',
        fields: [
          { name: 'email', type: 'string', 'x-janus-pattern': '^[a-z]+@[a-z]+\\.[a-z]+$' },
        ],
      } as AvroRecordType;

      const validator = avroToValidator(schema);
      expect(validator.validate({ email: 'test@example.com' }).valid).toBe(true);
      expect(validator.validate({ email: 'invalid' }).valid).toBe(false);
    });

    it('converts bytes type', () => {
      const validator = avroToValidator('bytes');
      expect(validator.validate(new Uint8Array([1, 2, 3])).valid).toBe(true);
      expect(validator.validate('not bytes').valid).toBe(false);
    });

    it('converts bytes type with length constraints', () => {
      const schema = {
        type: 'record',
        name: 'Test',
        fields: [
          { name: 'data', type: 'bytes', 'x-janus-minLength': 2, 'x-janus-maxLength': 4 },
        ],
      } as AvroRecordType;

      const validator = avroToValidator(schema);
      expect(validator.validate({ data: new Uint8Array([1, 2]) }).valid).toBe(true);
      expect(validator.validate({ data: new Uint8Array([1, 2, 3, 4]) }).valid).toBe(true);
      expect(validator.validate({ data: new Uint8Array([1]) }).valid).toBe(false);
      expect(validator.validate({ data: new Uint8Array([1, 2, 3, 4, 5]) }).valid).toBe(false);
    });
  });

  describe('record type', () => {
    it('converts simple record', () => {
      const schema: AvroRecordType = {
        type: 'record',
        name: 'User',
        fields: [
          { name: 'name', type: 'string' },
          { name: 'age', type: 'int' },
        ],
      };

      const validator = avroToValidator(schema);
      expect(validator.validate({ name: 'Alice', age: 30 }).valid).toBe(true);
      expect(validator.validate({ name: 'Bob' }).valid).toBe(false); // missing age
      expect(validator.validate({ name: 123, age: 30 }).valid).toBe(false); // wrong type
    });

    it('converts record with nested record', () => {
      const schema: AvroRecordType = {
        type: 'record',
        name: 'User',
        fields: [
          { name: 'name', type: 'string' },
          {
            name: 'address',
            type: {
              type: 'record',
              name: 'Address',
              fields: [
                { name: 'street', type: 'string' },
                { name: 'city', type: 'string' },
              ],
            },
          },
        ],
      };

      const validator = avroToValidator(schema);
      expect(
        validator.validate({
          name: 'Alice',
          address: { street: '123 Main St', city: 'Boston' },
        }).valid
      ).toBe(true);
    });

    it('allows extra fields in non-strict mode (default)', () => {
      const schema: AvroRecordType = {
        type: 'record',
        name: 'User',
        fields: [{ name: 'name', type: 'string' }],
      };

      const validator = avroToValidator(schema);
      expect(validator.validate({ name: 'Alice', extra: 'field' }).valid).toBe(true);
    });

    it('rejects extra fields in strict mode', () => {
      const schema: AvroRecordType = {
        type: 'record',
        name: 'User',
        fields: [{ name: 'name', type: 'string' }],
      };

      const validator = avroToValidator(schema, { strict: true });
      expect(validator.validate({ name: 'Alice' }).valid).toBe(true);
      expect(validator.validate({ name: 'Alice', extra: 'field' }).valid).toBe(false);
    });
  });

  describe('union type', () => {
    it('converts union with null (optional field)', () => {
      const schema: AvroRecordType = {
        type: 'record',
        name: 'User',
        fields: [{ name: 'nickname', type: ['null', 'string'] }],
      };

      const validator = avroToValidator(schema);
      expect(validator.validate({ nickname: 'Al' }).valid).toBe(true);
      expect(validator.validate({ nickname: null }).valid).toBe(true);
      expect(validator.validate({ nickname: 123 }).valid).toBe(false);
    });

    it('converts union of multiple types', () => {
      const schema: AvroRecordType = {
        type: 'record',
        name: 'Value',
        fields: [{ name: 'data', type: ['string', 'int', 'boolean'] }],
      };

      const validator = avroToValidator(schema);
      expect(validator.validate({ data: 'hello' }).valid).toBe(true);
      expect(validator.validate({ data: 42 }).valid).toBe(true);
      expect(validator.validate({ data: true }).valid).toBe(true);
      expect(validator.validate({ data: 3.14 }).valid).toBe(false);
    });
  });

  describe('array type', () => {
    it('converts simple array', () => {
      const schema: AvroRecordType = {
        type: 'record',
        name: 'Test',
        fields: [
          {
            name: 'numbers',
            type: { type: 'array', items: 'int' } as AvroArrayType,
          },
        ],
      };

      const validator = avroToValidator(schema);
      expect(validator.validate({ numbers: [1, 2, 3] }).valid).toBe(true);
      expect(validator.validate({ numbers: [] }).valid).toBe(true);
      expect(validator.validate({ numbers: [1, 'two', 3] }).valid).toBe(false);
    });

    it('converts array with item constraints', () => {
      const schema: AvroRecordType = {
        type: 'record',
        name: 'Test',
        fields: [
          {
            name: 'tags',
            type: { type: 'array', items: 'string' } as AvroArrayType,
            'x-janus-minItems': 1,
            'x-janus-maxItems': 5,
          },
        ],
      };

      const validator = avroToValidator(schema);
      expect(validator.validate({ tags: ['a'] }).valid).toBe(true);
      expect(validator.validate({ tags: ['a', 'b', 'c', 'd', 'e'] }).valid).toBe(true);
      expect(validator.validate({ tags: [] }).valid).toBe(false);
      expect(validator.validate({ tags: ['a', 'b', 'c', 'd', 'e', 'f'] }).valid).toBe(false);
    });
  });

  describe('enum type', () => {
    it('converts enum', () => {
      const schema: AvroEnumType = {
        type: 'enum',
        name: 'Status',
        symbols: ['PENDING', 'ACTIVE', 'CLOSED'],
      };

      const validator = avroToValidator(schema);
      expect(validator.validate('PENDING').valid).toBe(true);
      expect(validator.validate('ACTIVE').valid).toBe(true);
      expect(validator.validate('CLOSED').valid).toBe(true);
      expect(validator.validate('UNKNOWN').valid).toBe(false);
    });

    it('converts single-symbol enum', () => {
      const schema: AvroEnumType = {
        type: 'enum',
        name: 'SingleValue',
        symbols: ['ONLY'],
      };

      const validator = avroToValidator(schema);
      expect(validator.validate('ONLY').valid).toBe(true);
      expect(validator.validate('OTHER').valid).toBe(false);
    });
  });

  describe('fixed type', () => {
    it('converts fixed to exact-length bytes', () => {
      const schema = {
        type: 'fixed',
        name: 'MD5',
        size: 16,
      };

      const validator = avroToValidator(schema as any);
      expect(validator.validate(new Uint8Array(16)).valid).toBe(true);
      expect(validator.validate(new Uint8Array(15)).valid).toBe(false);
      expect(validator.validate(new Uint8Array(17)).valid).toBe(false);
    });
  });

  describe('map type', () => {
    it('converts map to non-strict struct (per ADR-001)', () => {
      const schema: AvroRecordType = {
        type: 'record',
        name: 'Test',
        fields: [
          {
            name: 'metadata',
            type: { type: 'map', values: 'string' },
          },
        ],
      };

      const validator = avroToValidator(schema);
      // Map becomes non-strict struct, so any object is accepted
      expect(validator.validate({ metadata: { key1: 'value1' } }).valid).toBe(true);
      expect(validator.validate({ metadata: {} }).valid).toBe(true);
      // Note: per ADR-001, values are NOT validated
      expect(validator.validate({ metadata: { key1: 123 } }).valid).toBe(true);
    });
  });

  describe('x-janus-enum extension', () => {
    it('converts field with x-janus-enum to finite values', () => {
      const schema: AvroRecordType = {
        type: 'record',
        name: 'Test',
        fields: [
          {
            name: 'status',
            type: 'string',
            'x-janus-enum': ['active', 'inactive', 'pending'],
          },
        ],
      };

      const validator = avroToValidator(schema);
      expect(validator.validate({ status: 'active' }).valid).toBe(true);
      expect(validator.validate({ status: 'inactive' }).valid).toBe(true);
      expect(validator.validate({ status: 'unknown' }).valid).toBe(false);
    });
  });

  describe('generation', () => {
    it('generates valid values for record schema', () => {
      const schema: AvroRecordType = {
        type: 'record',
        name: 'User',
        fields: [
          { name: 'name', type: 'string', 'x-janus-minLength': 1, 'x-janus-maxLength': 50 },
          { name: 'age', type: 'int', 'x-janus-min': 0, 'x-janus-max': 150 },
          { name: 'active', type: 'boolean' },
        ],
      };

      const validator = avroToValidator(schema);
      const generator = new Generator(createRng());

      // Generate 10 values and verify they all validate
      for (let i = 0; i < 10; i++) {
        const value = generator.generate(validator.domain);
        const result = validator.validate(value);
        expect(result.valid).toBe(true);
      }
    });

    it('generates valid values for nested schema', () => {
      const schema: AvroRecordType = {
        type: 'record',
        name: 'Order',
        fields: [
          { name: 'id', type: 'string' },
          {
            name: 'items',
            type: { type: 'array', items: 'string' },
            'x-janus-minItems': 1,
            'x-janus-maxItems': 5,
          },
        ],
      };

      const validator = avroToValidator(schema);
      const generator = new Generator(createRng());

      for (let i = 0; i < 10; i++) {
        const value = generator.generate(validator.domain);
        const result = validator.validate(value);
        expect(result.valid).toBe(true);
      }
    });
  });
});


