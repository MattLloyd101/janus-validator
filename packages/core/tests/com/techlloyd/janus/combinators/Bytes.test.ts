import { Bytes } from '@/com/techlloyd/janus/combinators/Bytes';
import { Generator } from '@/com/techlloyd/janus/Generator';
import { DomainType, BytesDomain } from '@/com/techlloyd/janus/Domain';

describe('Bytes', () => {
  describe('validation', () => {
    it('should accept a valid Uint8Array', () => {
      const validator = Bytes(0, 100);
      const result = validator.validate(new Uint8Array([1, 2, 3, 4, 5]));
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBeInstanceOf(Uint8Array);
        expect(result.value.length).toBe(5);
      }
    });

    it('should accept an empty Uint8Array when minLength is 0', () => {
      const validator = Bytes(0, 100);
      const result = validator.validate(new Uint8Array(0));
      expect(result.valid).toBe(true);
    });

    it('should accept a Buffer (Node.js) and convert to Uint8Array', () => {
      const validator = Bytes(0, 100);
      const buffer = Buffer.from([1, 2, 3, 4, 5]);
      const result = validator.validate(buffer);
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBeInstanceOf(Uint8Array);
        expect(result.value.length).toBe(5);
      }
    });

    it('should reject Uint8Array shorter than minLength', () => {
      const validator = Bytes(10, 100);
      const result = validator.validate(new Uint8Array([1, 2, 3]));
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('less than minimum');
      }
    });

    it('should reject Uint8Array longer than maxLength', () => {
      const validator = Bytes(0, 5);
      const result = validator.validate(new Uint8Array(10));
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('greater than maximum');
      }
    });

    it('should reject non-binary types', () => {
      const validator = Bytes();
      
      expect(validator.validate('hello').valid).toBe(false);
      expect(validator.validate(123).valid).toBe(false);
      expect(validator.validate([1, 2, 3]).valid).toBe(false);
      expect(validator.validate({ length: 5 }).valid).toBe(false);
      expect(validator.validate(null).valid).toBe(false);
      expect(validator.validate(undefined).valid).toBe(false);
    });

    it('should use default min/max when not specified', () => {
      const validator = Bytes();
      // Default is minLength=0, maxLength=1024
      const result = validator.validate(new Uint8Array(500));
      expect(result.valid).toBe(true);
    });

    it('should work as fixed-length when min equals max', () => {
      // Bytes(n, n) is equivalent to Avro "fixed" type
      const fixed16 = Bytes(16, 16);
      
      expect(fixed16.validate(new Uint8Array(16)).valid).toBe(true);
      expect(fixed16.validate(new Uint8Array(15)).valid).toBe(false);
      expect(fixed16.validate(new Uint8Array(17)).valid).toBe(false);
    });
  });

  describe('domain', () => {
    it('should have BYTES_DOMAIN type', () => {
      const validator = Bytes(10, 50);
      expect(validator.domain.type).toBe(DomainType.BYTES_DOMAIN);
    });

    it('should store minLength and maxLength in domain', () => {
      const validator = Bytes(10, 50);
      const domain = validator.domain as BytesDomain;
      expect(domain.minLength).toBe(10);
      expect(domain.maxLength).toBe(50);
    });
  });

  describe('error cases', () => {
    it('should throw if minLength is negative', () => {
      expect(() => Bytes(-1, 100)).toThrow('minLength must be non-negative');
    });

    it('should throw if maxLength is less than minLength', () => {
      expect(() => Bytes(100, 50)).toThrow('maxLength must be greater than or equal to minLength');
    });
  });

  describe('generation', () => {
    it('should generate valid Uint8Array within bounds', () => {
      const validator = Bytes(10, 20);
      const generator = new Generator({ random: Math.random });
      
      for (let i = 0; i < 10; i++) {
        const value = generator.generate(validator);
        expect(value).toBeInstanceOf(Uint8Array);
        expect(value.length).toBeGreaterThanOrEqual(10);
        expect(value.length).toBeLessThanOrEqual(20);
        
        // Verify all bytes are in valid range (0-255)
        for (const byte of value) {
          expect(byte).toBeGreaterThanOrEqual(0);
          expect(byte).toBeLessThanOrEqual(255);
        }
      }
    });

    it('should generate values that pass validation', () => {
      const validator = Bytes(5, 15);
      const generator = new Generator({ random: Math.random });
      
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        const result = validator.validate(value);
        expect(result.valid).toBe(true);
      }
    });

    it('should generate empty array when minLength is 0', () => {
      const validator = Bytes(0, 0);
      const generator = new Generator({ random: Math.random });
      
      const value = generator.generate(validator);
      expect(value.length).toBe(0);
    });
  });
});

