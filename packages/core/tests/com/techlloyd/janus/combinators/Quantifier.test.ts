import { Quantifier } from '@/com/techlloyd/janus/combinators/Quantifier';
import { Integer } from '@/com/techlloyd/janus/combinators/Integer';
import { UnicodeString } from '@/com/techlloyd/janus/combinators/UnicodeString';
import { Boolean } from '@/com/techlloyd/janus/combinators/Boolean';
import { DomainType, RNG, Generator } from '@/com/techlloyd/janus/index';

describe('Quantifier (Generic Combinator)', () => {
  describe('validation', () => {
    it('should validate arrays within min/max bounds', () => {
      const quantifier = new Quantifier(Integer(0, 100), 2, 4);

      expect(quantifier.validate([10, 20]).valid).toBe(true);
      expect(quantifier.validate([10, 20, 30]).valid).toBe(true);
      expect(quantifier.validate([10, 20, 30, 40]).valid).toBe(true);
    });

    it('should reject arrays below min length', () => {
      const quantifier = new Quantifier(Integer(0, 100), 2, 4);

      const result = quantifier.validate([10]);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('at least 2');
      }
    });

    it('should reject arrays above max length', () => {
      const quantifier = new Quantifier(Integer(0, 100), 2, 4);

      const result = quantifier.validate([10, 20, 30, 40, 50]);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('at most 4');
      }
    });

    it('should reject if any element fails validation', () => {
      const quantifier = new Quantifier(Integer(0, 100), 1, 5);

      const result = quantifier.validate([10, 200, 30]);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('[1]');
      }
    });

    it('should reject non-array values', () => {
      const quantifier = new Quantifier(Integer(0, 100), 1, 5);

      expect(quantifier.validate(123).valid).toBe(false);
      expect(quantifier.validate('hello').valid).toBe(false);
      expect(quantifier.validate({ length: 3 }).valid).toBe(false);
    });

    it('should handle zero min (optional)', () => {
      const quantifier = new Quantifier(Integer(0, 100), 0, 3);

      expect(quantifier.validate([]).valid).toBe(true);
      expect(quantifier.validate([10]).valid).toBe(true);
      expect(quantifier.validate([10, 20, 30]).valid).toBe(true);
    });

    it('should handle unbounded max (Infinity)', () => {
      const quantifier = new Quantifier(Integer(0, 100), 1, Infinity);

      expect(quantifier.validate([10]).valid).toBe(true);
      expect(quantifier.validate([10, 20, 30, 40, 50, 60, 70, 80, 90, 100]).valid).toBe(true);
    });

    it('should return validated values', () => {
      const quantifier = new Quantifier(Integer(0, 100), 2, 4);

      const result = quantifier.validate([10, 20, 30]);
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toEqual([10, 20, 30]);
      }
    });
  });

  describe('domain', () => {
    it('should expose a QuantifierDomain type', () => {
      const quantifier = new Quantifier(Integer(0, 100), 1, 5);
      expect(quantifier.domain.type).toBe(DomainType.QUANTIFIER_DOMAIN);
    });

    it('should contain the inner validator domain', () => {
      const inner = Integer(0, 100);
      const quantifier = new Quantifier(inner, 1, 5);

      expect(quantifier.domain.inner).toEqual(inner.domain);
      expect(quantifier.domain.min).toBe(1);
      expect(quantifier.domain.max).toBe(5);
    });
  });

  describe('generation', () => {
    it('should generate arrays within bounds', () => {
      const quantifier = new Quantifier(Integer(0, 100), 2, 5);

      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(quantifier) as number[];
        expect(Array.isArray(value)).toBe(true);
        expect(value.length).toBeGreaterThanOrEqual(2);
        expect(value.length).toBeLessThanOrEqual(5);
        value.forEach(v => {
          expect(v).toBeGreaterThanOrEqual(0);
          expect(v).toBeLessThanOrEqual(100);
        });
      }
    });

    it('should generate values that pass validation', () => {
      const quantifier = new Quantifier(UnicodeString(1, 10), 1, 5);

      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 100; i++) {
        const value = generator.generate(quantifier);
        const result = quantifier.validate(value);
        expect(result.valid).toBe(true);
      }
    });

    it('should handle unbounded max with default cap', () => {
      const quantifier = new Quantifier(Integer(0, 10), 1, Infinity);

      const rng: RNG = { random: () => 0.99 }; // Should hit the cap
      const generator = new Generator(rng);
      const value = generator.generate(quantifier) as number[];

      // Default cap is 10
      expect(value.length).toBeLessThanOrEqual(10);
    });

    it('should generate empty array when min is 0 and rng favors it', () => {
      const quantifier = new Quantifier(Integer(0, 10), 0, 5);

      const rng: RNG = { random: () => 0 }; // Will pick min
      const generator = new Generator(rng);
      const value = generator.generate(quantifier) as number[];

      expect(value).toEqual([]);
    });
  });

  describe('factory methods', () => {
    it('zeroOrMore should create 0 to Infinity quantifier', () => {
      const q = Quantifier.zeroOrMore(Integer(0, 10));
      expect(q.min).toBe(0);
      expect(q.max).toBe(Infinity);
    });

    it('oneOrMore should create 1 to Infinity quantifier', () => {
      const q = Quantifier.oneOrMore(Integer(0, 10));
      expect(q.min).toBe(1);
      expect(q.max).toBe(Infinity);
    });

    it('optional should create 0 to 1 quantifier', () => {
      const q = Quantifier.optional(Integer(0, 10));
      expect(q.min).toBe(0);
      expect(q.max).toBe(1);
    });

    it('exactly should create n to n quantifier', () => {
      const q = Quantifier.exactly(Integer(0, 10), 5);
      expect(q.min).toBe(5);
      expect(q.max).toBe(5);
    });

    it('atLeast should create n to Infinity quantifier', () => {
      const q = Quantifier.atLeast(Integer(0, 10), 3);
      expect(q.min).toBe(3);
      expect(q.max).toBe(Infinity);
    });

    it('between should create min to max quantifier', () => {
      const q = Quantifier.between(Integer(0, 10), 2, 7);
      expect(q.min).toBe(2);
      expect(q.max).toBe(7);
    });
  });

  describe('edge cases', () => {
    it('should handle exactly(0) for empty arrays only', () => {
      const q = Quantifier.exactly(Integer(0, 10), 0);

      expect(q.validate([]).valid).toBe(true);
      expect(q.validate([1]).valid).toBe(false);
    });

    it('should handle exactly(1) for single element arrays', () => {
      const q = Quantifier.exactly(Boolean(), 1);

      expect(q.validate([true]).valid).toBe(true);
      expect(q.validate([false]).valid).toBe(true);
      expect(q.validate([]).valid).toBe(false);
      expect(q.validate([true, false]).valid).toBe(false);
    });

    it('should work with different validator types', () => {
      const intQ = Quantifier.between(Integer(0, 100), 1, 3);
      const strQ = Quantifier.between(UnicodeString(1, 5), 1, 3);
      const boolQ = Quantifier.between(Boolean(), 1, 3);

      expect(intQ.validate([10, 20]).valid).toBe(true);
      expect(strQ.validate(['a', 'bc']).valid).toBe(true);
      expect(boolQ.validate([true, false]).valid).toBe(true);
    });
  });
});

