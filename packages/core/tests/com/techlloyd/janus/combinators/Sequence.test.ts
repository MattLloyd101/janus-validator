import { Sequence } from '@/com/techlloyd/janus/combinators/Sequence';
import { Integer } from '@/com/techlloyd/janus/combinators/Integer';
import { UnicodeString } from '@/com/techlloyd/janus/combinators/UnicodeString';
import { Boolean } from '@/com/techlloyd/janus/combinators/Boolean';
import { DomainType, RNG, Generator } from '@/com/techlloyd/janus/index';

describe('Sequence (Generic Combinator)', () => {
  describe('validation', () => {
    it('should validate array elements against corresponding validators', () => {
      const sequence = new Sequence(
        Integer(0, 100),
        UnicodeString(1, 5),
        Boolean()
      );

      expect(sequence.validate([50, 'abc', true]).valid).toBe(true);
      expect(sequence.validate([0, 'x', false]).valid).toBe(true);
    });

    it('should fail if array length does not match validators', () => {
      const sequence = new Sequence(Integer(0, 10), UnicodeString(1, 5));

      const result1 = sequence.validate([5]);
      expect(result1.valid).toBe(false);
      if (!result1.valid) {
        expect(result1.error).toContain('length');
      }

      const result2 = sequence.validate([5, 'abc', 'extra']);
      expect(result2.valid).toBe(false);
      if (!result2.valid) {
        expect(result2.error).toContain('length');
      }
    });

    it('should fail if any element fails validation', () => {
      const sequence = new Sequence(Integer(0, 10), UnicodeString(1, 5));

      const result = sequence.validate([50, 'abc']); // 50 is out of range
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('[0]');
      }
    });

    it('should report which index failed', () => {
      const sequence = new Sequence(Integer(0, 100), UnicodeString(1, 5));

      const result = sequence.validate([50, 'toolongstring']);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('[1]');
      }
    });

    it('should reject non-array values', () => {
      const sequence = new Sequence(Integer(0, 10));

      expect(sequence.validate(5).valid).toBe(false);
      expect(sequence.validate('hello').valid).toBe(false);
      expect(sequence.validate({ 0: 5 }).valid).toBe(false);
    });

    it('should handle empty sequence (validates empty arrays)', () => {
      const sequence = new Sequence();
      
      expect(sequence.validate([]).valid).toBe(true);
      expect(sequence.validate([1]).valid).toBe(false);
    });

    it('should return validated values', () => {
      const sequence = new Sequence(Integer(0, 100), UnicodeString(1, 10));

      const result = sequence.validate([42, 'hello']);
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toEqual([42, 'hello']);
      }
    });
  });

  describe('domain', () => {
    it('should expose a SequenceDomain type', () => {
      const sequence = new Sequence(Integer(0, 10), UnicodeString(1, 5));
      expect(sequence.domain.type).toBe(DomainType.SEQUENCE_DOMAIN);
    });

    it('should contain the domains of its child validators as parts', () => {
      const v1 = Integer(0, 10);
      const v2 = UnicodeString(1, 5);
      const sequence = new Sequence(v1, v2);

      expect(sequence.domain.parts).toEqual([
        v1.domain,
        v2.domain,
      ]);
    });
  });

  describe('generation', () => {
    it('should generate an array with one value per validator', () => {
      const sequence = new Sequence(Integer(0, 100), UnicodeString(1, 5), Boolean());

      const rng: RNG = { random: () => 0.5 };
      const generator = new Generator(rng);
      const value = generator.generate(sequence) as any[];

      expect(Array.isArray(value)).toBe(true);
      expect(value.length).toBe(3);
      expect(typeof value[0]).toBe('number');
      expect(typeof value[1]).toBe('string');
      expect(typeof value[2]).toBe('boolean');
    });

    it('should generate values that pass validation', () => {
      const sequence = new Sequence(Integer(0, 100), UnicodeString(1, 10));

      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 100; i++) {
        const value = generator.generate(sequence);
        const result = sequence.validate(value);
        expect(result.valid).toBe(true);
      }
    });

    it('should generate empty array for empty sequence', () => {
      const sequence = new Sequence();

      const rng: RNG = { random: () => 0.5 };
      const generator = new Generator(rng);
      const value = generator.generate(sequence);

      expect(value).toEqual([]);
    });
  });

  describe('static of factory', () => {
    it('should handle empty validators', () => {
      const result = Sequence.of();
      expect(result).toBeInstanceOf(Sequence);
      expect((result as Sequence).validators.length).toBe(0);
    });

    it('should return Sequence for any number of validators', () => {
      const v1 = Integer(0, 10);
      const result = Sequence.of(v1);
      expect(result).toBeInstanceOf(Sequence);
    });

    it('should return Sequence for multiple validators', () => {
      const v1 = Integer(0, 10);
      const v2 = UnicodeString(1, 5);
      const result = Sequence.of(v1, v2);
      expect(result).toBeInstanceOf(Sequence);
    });
  });
});

