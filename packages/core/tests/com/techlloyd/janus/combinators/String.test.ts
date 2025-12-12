import {
  String,
  digits,
  lower,
  upper,
  letters,
  alphanumeric,
  hex,
  hexUpper,
  chars,
} from '@/com/techlloyd/janus/combinators/String';
import { Generator } from '@/com/techlloyd/janus/Generator';

describe('String (Compound String Combinator)', () => {
  describe('basic validation', () => {
    it('should validate a simple literal pattern', () => {
      const validator = String('hello');
      expect(validator.validate('hello').valid).toBe(true);
      expect(validator.validate('world').valid).toBe(false);
    });

    it('should validate digits pattern', () => {
      const validator = String(digits(4));
      expect(validator.validate('1234').valid).toBe(true);
      expect(validator.validate('123').valid).toBe(false);
      expect(validator.validate('12345').valid).toBe(false);
      expect(validator.validate('abcd').valid).toBe(false);
    });

    it('should validate combined literal and digits', () => {
      const validator = String('ID-', digits(4));
      expect(validator.validate('ID-1234').valid).toBe(true);
      expect(validator.validate('ID-123').valid).toBe(false);
      expect(validator.validate('XX-1234').valid).toBe(false);
    });
  });

  describe('date format (YYYY-MM-DD)', () => {
    const ISODate = String(digits(4), '-', digits(2), '-', digits(2));

    it('should validate valid ISO dates', () => {
      expect(ISODate.validate('2024-01-15').valid).toBe(true);
      expect(ISODate.validate('1999-12-31').valid).toBe(true);
    });

    it('should reject invalid ISO dates', () => {
      expect(ISODate.validate('24-01-15').valid).toBe(false);
      expect(ISODate.validate('2024/01/15').valid).toBe(false);
      expect(ISODate.validate('2024-1-15').valid).toBe(false);
    });
  });

  describe('phone format ((XXX) XXX-XXXX)', () => {
    const Phone = String('(', digits(3), ') ', digits(3), '-', digits(4));

    it('should validate valid phone numbers', () => {
      expect(Phone.validate('(555) 123-4567').valid).toBe(true);
      expect(Phone.validate('(800) 555-1234').valid).toBe(true);
    });

    it('should reject invalid phone numbers', () => {
      expect(Phone.validate('555-123-4567').valid).toBe(false);
      expect(Phone.validate('(555)123-4567').valid).toBe(false);
      expect(Phone.validate('(55) 123-4567').valid).toBe(false);
    });
  });

  describe('UUID format', () => {
    const UUID = String(
      hex(8), '-', hex(4), '-', hex(4), '-', hex(4), '-', hex(12)
    );

    it('should validate valid UUIDs', () => {
      expect(UUID.validate('a1b2c3d4-e5f6-7890-abcd-ef1234567890').valid).toBe(true);
      expect(UUID.validate('00000000-0000-0000-0000-000000000000').valid).toBe(true);
    });

    it('should reject invalid UUIDs', () => {
      expect(UUID.validate('a1b2c3d4e5f67890abcdef1234567890').valid).toBe(false);
      expect(UUID.validate('a1b2c3d4-e5f6-7890-abcd').valid).toBe(false);
      expect(UUID.validate('g1b2c3d4-e5f6-7890-abcd-ef1234567890').valid).toBe(false);
    });
  });

  describe('character set validators', () => {
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
    });

    describe('lower', () => {
      it('should validate lowercase letters', () => {
        const v = lower(3);
        expect(v.validate('abc').valid).toBe(true);
        expect(v.validate('ABC').valid).toBe(false);
        expect(v.validate('ab1').valid).toBe(false);
      });
    });

    describe('upper', () => {
      it('should validate uppercase letters', () => {
        const v = upper(3);
        expect(v.validate('ABC').valid).toBe(true);
        expect(v.validate('abc').valid).toBe(false);
        expect(v.validate('AB1').valid).toBe(false);
      });
    });

    describe('letters', () => {
      it('should validate mixed case letters', () => {
        const v = letters(3);
        expect(v.validate('AbC').valid).toBe(true);
        expect(v.validate('abc').valid).toBe(true);
        expect(v.validate('ABC').valid).toBe(true);
        expect(v.validate('ab1').valid).toBe(false);
      });
    });

    describe('alphanumeric', () => {
      it('should validate letters and digits', () => {
        const v = alphanumeric(4);
        expect(v.validate('Ab12').valid).toBe(true);
        expect(v.validate('abcd').valid).toBe(true);
        expect(v.validate('1234').valid).toBe(true);
        expect(v.validate('ab-1').valid).toBe(false);
      });
    });

    describe('hex', () => {
      it('should validate lowercase hex', () => {
        const v = hex(6);
        expect(v.validate('a1b2c3').valid).toBe(true);
        expect(v.validate('ffffff').valid).toBe(true);
        expect(v.validate('AABBCC').valid).toBe(false);
        expect(v.validate('ghijkl').valid).toBe(false);
      });
    });

    describe('hexUpper', () => {
      it('should validate uppercase hex', () => {
        const v = hexUpper(6);
        expect(v.validate('A1B2C3').valid).toBe(true);
        expect(v.validate('FFFFFF').valid).toBe(true);
        expect(v.validate('aabbcc').valid).toBe(false);
      });
    });

    describe('chars', () => {
      it('should validate custom character set', () => {
        const v = chars('abc123', 4);
        expect(v.validate('a1b2').valid).toBe(true);
        expect(v.validate('abca').valid).toBe(true);
        expect(v.validate('1111').valid).toBe(true);
        expect(v.validate('abcd').valid).toBe(false);
      });
    });
  });

  describe('generation', () => {
    const generator = new Generator({ random: Math.random });

    it('should generate valid ISO dates', () => {
      const ISODate = String(digits(4), '-', digits(2), '-', digits(2));
      
      for (let i = 0; i < 10; i++) {
        const value = generator.generate(ISODate.domain);
        const result = ISODate.validate(value);
        expect(result.valid).toBe(true);
        expect(value).toMatch(/^\d{4}-\d{2}-\d{2}$/);
      }
    });

    it('should generate valid phone numbers', () => {
      const Phone = String('(', digits(3), ') ', digits(3), '-', digits(4));
      
      for (let i = 0; i < 10; i++) {
        const value = generator.generate(Phone.domain);
        const result = Phone.validate(value);
        expect(result.valid).toBe(true);
        expect(value).toMatch(/^\(\d{3}\) \d{3}-\d{4}$/);
      }
    });

    it('should generate valid UUIDs', () => {
      const UUID = String(
        hex(8), '-', hex(4), '-', hex(4), '-', hex(4), '-', hex(12)
      );
      
      for (let i = 0; i < 10; i++) {
        const value = generator.generate(UUID.domain);
        const result = UUID.validate(value);
        expect(result.valid).toBe(true);
        expect(value).toMatch(/^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/);
      }
    });

    it('should generate valid credit card numbers', () => {
      const CreditCard = String(
        digits(4), ' ', digits(4), ' ', digits(4), ' ', digits(4)
      );
      
      for (let i = 0; i < 10; i++) {
        const value = generator.generate(CreditCard.domain);
        const result = CreditCard.validate(value);
        expect(result.valid).toBe(true);
        expect(value).toMatch(/^\d{4} \d{4} \d{4} \d{4}$/);
      }
    });

    it('should generate values from variable-length parts', () => {
      const Code = String(letters(2, 4), '-', digits(3, 5));
      
      for (let i = 0; i < 10; i++) {
        const value = generator.generate(Code.domain);
        const result = Code.validate(value);
        expect(result.valid).toBe(true);
        expect(value).toMatch(/^[a-zA-Z]{2,4}-\d{3,5}$/);
      }
    });
  });

  describe('edge cases', () => {
    it('should handle empty string pattern', () => {
      const validator = String();
      expect(validator.validate('').valid).toBe(true);
      expect(validator.validate('x').valid).toBe(false);
    });

    it('should handle single literal', () => {
      const validator = String('prefix');
      expect(validator.validate('prefix').valid).toBe(true);
      expect(validator.validate('').valid).toBe(false);
    });

    it('should handle consecutive literals', () => {
      const validator = String('hello', ' ', 'world');
      expect(validator.validate('hello world').valid).toBe(true);
    });

    it('should provide error messages', () => {
      const validator = String('ID-', digits(4));
      const result = validator.validate('XX-1234');
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('Expected');
      }
    });
  });
});
