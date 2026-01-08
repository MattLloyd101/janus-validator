import {
  CompoundString,
  digits,
  lower,
  upper,
  letters,
  alphanumeric,
  hex,
  hexUpper,
  chars,
} from '@/com/techlloyd/janus/combinators/CompoundString';
import { Generator } from '@/com/techlloyd/janus/Generator';

describe('CompoundString', () => {
  describe('basic validation', () => {
    it('should validate a simple literal pattern', () => {
      const validator = CompoundString('hello');
      expect(validator.validate('hello').valid).toBe(true);
      expect(validator.validate('world').valid).toBe(false);
    });

    it('should validate digits pattern', () => {
      const validator = CompoundString(digits(4));
      expect(validator.validate('1234').valid).toBe(true);
      expect(validator.validate('123').valid).toBe(false);
      expect(validator.validate('12345').valid).toBe(false);
      expect(validator.validate('abcd').valid).toBe(false);
    });

    it('should validate combined literal and digits', () => {
      const validator = CompoundString('ID-', digits(4));
      expect(validator.validate('ID-1234').valid).toBe(true);
      expect(validator.validate('ID-123').valid).toBe(false);
      expect(validator.validate('XX-1234').valid).toBe(false);
    });
  });

  describe('complex patterns', () => {
    it('should validate ISO date format', () => {
      const ISODate = CompoundString(digits(4), '-', digits(2), '-', digits(2));

      expect(ISODate.validate('2024-01-15').valid).toBe(true);
      expect(ISODate.validate('2024-1-15').valid).toBe(false);
      expect(ISODate.validate('20240115').valid).toBe(false);
      expect(ISODate.validate('2024/01/15').valid).toBe(false);
    });

    it('should validate US phone format', () => {
      const Phone = CompoundString('(', digits(3), ') ', digits(3), '-', digits(4));

      expect(Phone.validate('(555) 123-4567').valid).toBe(true);
      expect(Phone.validate('555-123-4567').valid).toBe(false);
      expect(Phone.validate('(555) 12-4567').valid).toBe(false);
    });

    it('should validate UUID format', () => {
      const UUID = CompoundString(
        hex(8), '-', hex(4), '-', hex(4), '-', hex(4), '-', hex(12)
      );

      expect(UUID.validate('123e4567-e89b-12d3-a456-426614174000').valid).toBe(true);
      expect(UUID.validate('123E4567-E89B-12D3-A456-426614174000').valid).toBe(false); // uppercase fails
      expect(UUID.validate('123e4567e89b12d3a456426614174000').valid).toBe(false); // no dashes
    });
  });

  describe('character classes', () => {
    describe('digits', () => {
      it('should validate exact count', () => {
        const v = digits(4);
        expect(v.validate('1234').valid).toBe(true);
        expect(v.validate('123').valid).toBe(false);
        expect(v.validate('12345').valid).toBe(false);
      });

      it('should validate range', () => {
        const v = digits(2, 4);
        expect(v.validate('12').valid).toBe(true);
        expect(v.validate('123').valid).toBe(true);
        expect(v.validate('1234').valid).toBe(true);
        expect(v.validate('1').valid).toBe(false);
        expect(v.validate('12345').valid).toBe(false);
      });

      it('should reject non-digits', () => {
        const v = digits(4);
        expect(v.validate('abcd').valid).toBe(false);
        expect(v.validate('12ab').valid).toBe(false);
      });
    });

    describe('lower', () => {
      it('should validate lowercase letters only', () => {
        const v = lower(4);
        expect(v.validate('abcd').valid).toBe(true);
        expect(v.validate('ABCD').valid).toBe(false);
        expect(v.validate('AbCd').valid).toBe(false);
        expect(v.validate('1234').valid).toBe(false);
      });
    });

    describe('upper', () => {
      it('should validate uppercase letters only', () => {
        const v = upper(4);
        expect(v.validate('ABCD').valid).toBe(true);
        expect(v.validate('abcd').valid).toBe(false);
        expect(v.validate('AbCd').valid).toBe(false);
      });
    });

    describe('letters', () => {
      it('should validate any letters', () => {
        const v = letters(4);
        expect(v.validate('abcd').valid).toBe(true);
        expect(v.validate('ABCD').valid).toBe(true);
        expect(v.validate('AbCd').valid).toBe(true);
        expect(v.validate('1234').valid).toBe(false);
      });
    });

    describe('alphanumeric', () => {
      it('should validate letters and digits', () => {
        const v = alphanumeric(4);
        expect(v.validate('ab12').valid).toBe(true);
        expect(v.validate('AB12').valid).toBe(true);
        expect(v.validate('1234').valid).toBe(true);
        expect(v.validate('ab-1').valid).toBe(false);
      });
    });

    describe('hex', () => {
      it('should validate lowercase hex', () => {
        const v = hex(4);
        expect(v.validate('1234').valid).toBe(true);
        expect(v.validate('abcd').valid).toBe(true);
        expect(v.validate('ABCD').valid).toBe(false);
        expect(v.validate('ghij').valid).toBe(false);
      });
    });

    describe('hexUpper', () => {
      it('should validate uppercase hex', () => {
        const v = hexUpper(4);
        expect(v.validate('1234').valid).toBe(true);
        expect(v.validate('ABCD').valid).toBe(true);
        expect(v.validate('abcd').valid).toBe(false);
      });
    });

    describe('chars', () => {
      it('should validate custom character set', () => {
        const v = chars('abc123', 4);
        expect(v.validate('ab12').valid).toBe(true);
        expect(v.validate('1abc').valid).toBe(true);
        expect(v.validate('xxxx').valid).toBe(false);
      });
    });
  });

  describe('generation', () => {
    const createGenerator = () => {
      let callCount = 0;
      return new Generator({
        random: () => {
          callCount++;
          return (callCount * 0.1) % 1;
        },
      });
    };

    it('should generate valid ISO dates', () => {
      const ISODate = CompoundString(digits(4), '-', digits(2), '-', digits(2));
      const generator = createGenerator();

      for (let i = 0; i < 10; i++) {
        const value = generator.generate(ISODate.domain);
        expect(ISODate.validate(value).valid).toBe(true);
        expect(value).toMatch(/^\d{4}-\d{2}-\d{2}$/);
      }
    });

    it('should generate valid phone numbers', () => {
      const Phone = CompoundString('(', digits(3), ') ', digits(3), '-', digits(4));
      const generator = createGenerator();

      for (let i = 0; i < 10; i++) {
        const value = generator.generate(Phone.domain);
        expect(Phone.validate(value).valid).toBe(true);
        expect(value).toMatch(/^\(\d{3}\) \d{3}-\d{4}$/);
      }
    });

    it('should generate valid UUIDs', () => {
      const UUID = CompoundString(
        hex(8), '-', hex(4), '-', hex(4), '-', hex(4), '-', hex(12)
      );
      const generator = createGenerator();

      for (let i = 0; i < 10; i++) {
        const value = generator.generate(UUID.domain);
        expect(UUID.validate(value).valid).toBe(true);
        expect(value).toMatch(/^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/);
      }
    });

    it('should generate valid credit card numbers', () => {
      const CreditCard = CompoundString(
        digits(4), ' ', digits(4), ' ', digits(4), ' ', digits(4)
      );
      const generator = createGenerator();

      for (let i = 0; i < 10; i++) {
        const value = generator.generate(CreditCard.domain);
        expect(CreditCard.validate(value).valid).toBe(true);
        expect(value).toMatch(/^\d{4} \d{4} \d{4} \d{4}$/);
      }
    });

    it('should generate valid variable-length codes', () => {
      const Code = CompoundString(letters(2, 4), '-', digits(3, 5));
      const generator = createGenerator();

      for (let i = 0; i < 10; i++) {
        const value = generator.generate(Code.domain);
        expect(Code.validate(value).valid).toBe(true);
        expect(value).toMatch(/^[a-zA-Z]{2,4}-\d{3,5}$/);
      }
    });
  });

  describe('domain', () => {
    it('should expose regex pattern in domain', () => {
      const validator = CompoundString();
      expect(validator.domain).toBeDefined();
    });

    it('should have correct domain for literal', () => {
      const validator = CompoundString('prefix');
      expect(validator.domain._parts).toEqual(['prefix']);
    });

    it('should have correct domain for compound', () => {
      const validator = CompoundString('hello', ' ', 'world');
      expect(validator.domain._parts).toHaveLength(3);
    });

    it('should track parts for generation', () => {
      const validator = CompoundString('ID-', digits(4));
      expect(validator.domain._parts).toHaveLength(2);
    });
  });

  describe('error messages', () => {
    it('should report position of mismatch', () => {
      const validator = CompoundString('prefix-', digits(4));
      const result = validator.validate('prefix-abc');

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('position');
      }
    });
  });
});

