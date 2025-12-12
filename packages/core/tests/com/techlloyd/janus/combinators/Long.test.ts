import { Long } from '@/com/techlloyd/janus/combinators/Long';
import { Generator } from '@/com/techlloyd/janus/Generator';
import { DomainType, BigIntDomain } from '@/com/techlloyd/janus/Domain';

describe('Long', () => {
  describe('validation', () => {
    it('should accept a bigint value', () => {
      const validator = Long();
      const result = validator.validate(42n);
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe(42n);
      }
    });

    it('should accept an integer number and convert to bigint', () => {
      const validator = Long();
      const result = validator.validate(42);
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe(42n);
        expect(typeof result.value).toBe('bigint');
      }
    });

    it('should accept a numeric string and convert to bigint', () => {
      const validator = Long();
      const result = validator.validate('9007199254740993'); // Beyond MAX_SAFE_INTEGER
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe(9007199254740993n);
      }
    });

    it('should accept negative values', () => {
      const validator = Long();
      const result = validator.validate(-9007199254740993n);
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe(-9007199254740993n);
      }
    });

    it('should reject non-integer numbers', () => {
      const validator = Long();
      const result = validator.validate(3.14);
      expect(result.valid).toBe(false);
    });

    it('should reject non-numeric strings', () => {
      const validator = Long();
      const result = validator.validate('not a number');
      expect(result.valid).toBe(false);
    });

    it('should accept negative number strings', () => {
      const validator = Long();
      const result = validator.validate('-9007199254740993');
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe(-9007199254740993n);
      }
    });

    it('should accept strings with whitespace', () => {
      const validator = Long();
      const result = validator.validate(' 123 ');
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe(123n);
      }
    });

    it('should reject decimal strings', () => {
      const validator = Long();
      const result = validator.validate('3.14');
      expect(result.valid).toBe(false);
    });

    it('should reject empty strings', () => {
      const validator = Long();
      const result = validator.validate('');
      expect(result.valid).toBe(false);
    });

    it('should reject whitespace-only strings', () => {
      const validator = Long();
      expect(validator.validate('   ').valid).toBe(false);
      expect(validator.validate('\t').valid).toBe(false);
      expect(validator.validate('\n').valid).toBe(false);
    });

    it('should reject values below minimum', () => {
      const validator = Long(0n, 100n);
      const result = validator.validate(-1n);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('less than minimum');
      }
    });

    it('should reject values above maximum', () => {
      const validator = Long(0n, 100n);
      const result = validator.validate(101n);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('greater than maximum');
      }
    });

    it('should reject non-numeric types', () => {
      const validator = Long();
      
      expect(validator.validate(null).valid).toBe(false);
      expect(validator.validate(undefined).valid).toBe(false);
      expect(validator.validate({}).valid).toBe(false);
      expect(validator.validate([]).valid).toBe(false);
      expect(validator.validate(true).valid).toBe(false);
    });
  });

  describe('range constraints', () => {
    it('should use default Avro long range', () => {
      const validator = Long();
      const domain = validator.domain as BigIntDomain;
      expect(domain.min).toBe(-(2n ** 63n));
      expect(domain.max).toBe(2n ** 63n - 1n);
    });

    it('should accept custom range', () => {
      const validator = Long(0n, 1000n);
      const domain = validator.domain as BigIntDomain;
      expect(domain.min).toBe(0n);
      expect(domain.max).toBe(1000n);
    });

    it('should handle values at exact boundaries', () => {
      const validator = Long(0n, 100n);
      expect(validator.validate(0n).valid).toBe(true);
      expect(validator.validate(100n).valid).toBe(true);
    });

    it('should handle very large 64-bit values', () => {
      const validator = Long();
      
      // Max 64-bit signed
      expect(validator.validate(9223372036854775807n).valid).toBe(true);
      
      // Min 64-bit signed
      expect(validator.validate(-9223372036854775808n).valid).toBe(true);
    });
  });

  describe('domain', () => {
    it('should have BIGINT_DOMAIN type', () => {
      const validator = Long();
      expect(validator.domain.type).toBe(DomainType.BIGINT_DOMAIN);
    });
  });

  describe('error cases', () => {
    it('should throw if min > max', () => {
      expect(() => Long(100n, 0n)).toThrow('min must be less than or equal to max');
    });
  });

  describe('generation', () => {
    it('should generate valid bigint within bounds', () => {
      const validator = Long(0n, 1000n);
      const generator = new Generator({ random: Math.random });
      
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator.domain);
        expect(typeof value).toBe('bigint');
        expect(value).toBeGreaterThanOrEqual(0n);
        expect(value).toBeLessThanOrEqual(1000n);
      }
    });

    it('should generate values that pass validation', () => {
      const validator = Long(-1000n, 1000n);
      const generator = new Generator({ random: Math.random });
      
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator.domain);
        const result = validator.validate(value);
        expect(result.valid).toBe(true);
      }
    });

    it('should generate for single-value range', () => {
      const validator = Long(42n, 42n);
      const generator = new Generator({ random: Math.random });
      
      const value = generator.generate(validator.domain);
      expect(value).toBe(42n);
    });

    it('should generate large 64-bit values', () => {
      // Use a smaller but still large range for testing
      const min = 9000000000000000000n;
      const max = 9223372036854775807n;
      const validator = Long(min, max);
      const generator = new Generator({ random: Math.random });
      
      for (let i = 0; i < 10; i++) {
        const value = generator.generate(validator.domain);
        expect(value).toBeGreaterThanOrEqual(min);
        expect(value).toBeLessThanOrEqual(max);
      }
    });
  });
});

