import { Sequence, RegexSequence } from '@/com/techlloyd/janus/combinators/regex/Sequence';
import { Literal } from '@/com/techlloyd/janus/combinators/regex/Literal';
import { CharClasses } from '@/com/techlloyd/janus/combinators/regex/CharClass';
import { Empty } from '@/com/techlloyd/janus/combinators/regex/Empty';
import { DomainType } from '@/com/techlloyd/janus/Domain';
import { RNG } from '@/com/techlloyd/janus/RNG';
import { Generator } from '@/com/techlloyd/janus/Generator';

describe('Sequence', () => {
  describe('matching', () => {
    it('should match validators in order', () => {
      const seq = new Sequence(
        new Literal('a'),
        new Literal('b'),
        new Literal('c')
      );
      const result = seq.match('abc', 0);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(3);
    });

    it('should fail if any validator fails', () => {
      const seq = new Sequence(
        new Literal('a'),
        new Literal('b'),
        new Literal('c')
      );
      expect(seq.match('abd', 0).matched).toBe(false);
      expect(seq.match('xbc', 0).matched).toBe(false);
    });

    it('should fail if string is too short', () => {
      const seq = new Sequence(
        new Literal('a'),
        new Literal('b'),
        new Literal('c')
      );
      expect(seq.match('ab', 0).matched).toBe(false);
    });

    it('should match at any position', () => {
      const seq = new Sequence(
        new Literal('b'),
        new Literal('c')
      );
      const result = seq.match('abc', 1);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(2);
    });

    it('should work with mixed validator types', () => {
      const seq = new Sequence(
        new Literal('a'),
        CharClasses.digit(),
        new Literal('z')
      );
      expect(seq.match('a5z', 0).matched).toBe(true);
      expect(seq.match('a9z', 0).matched).toBe(true);
      expect(seq.match('abz', 0).matched).toBe(false);
    });

    it('should handle empty sequence', () => {
      const seq = new Sequence();
      const result = seq.match('abc', 0);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(0);
    });
  });

  describe('validation', () => {
    it('should validate exact match', () => {
      const seq = new Sequence(
        new Literal('h'),
        new Literal('i')
      );
      expect(seq.validate('hi').valid).toBe(true);
    });

    it('should reject partial matches', () => {
      const seq = new Sequence(
        new Literal('h'),
        new Literal('i')
      );
      expect(seq.validate('h').valid).toBe(false);
      expect(seq.validate('hii').valid).toBe(false);
    });

    it('should reject non-strings', () => {
      const seq = new Sequence(new Literal('a'));
      expect(seq.validate(123).valid).toBe(false);
    });
  });

  describe('generation', () => {
    it('should generate by concatenating each validator output', () => {
      const seq = new Sequence(
        new Literal('h'),
        new Literal('e'),
        new Literal('l'),
        new Literal('l'),
        new Literal('o')
      );
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);
      expect(generator.generate(seq.domain)).toBe('hello');
    });

    it('should generate with mixed validators', () => {
      const seq = new Sequence(
        new Literal('a'),
        CharClasses.digit(),
        new Literal('z')
      );
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(seq.domain);
        expect(value.length).toBe(3);
        expect(value[0]).toBe('a');
        expect(value[1]).toMatch(/\d/);
        expect(value[2]).toBe('z');
      }
    });

    it('should generate empty string for empty sequence', () => {
      const seq = new Sequence();
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);
      expect(generator.generate(seq.domain)).toBe('');
    });
  });

  describe('domain', () => {
    it('should concatenate sources', () => {
      const seq = new Sequence(
        new Literal('a'),
        new Literal('b'),
        new Literal('c')
      );
      expect(seq.domain.type).toBe(DomainType.REGEX_DOMAIN);
      expect(seq.domain.source).toBe('abc');
    });
  });

  describe('RegexSequence.create factory', () => {
    it('should flatten nested sequences', () => {
      const inner = new Sequence(new Literal('a'), new Literal('b'));
      const outer = RegexSequence.create(inner, new Literal('c'));
      
      // Should behave as if it's a flat sequence
      expect(outer.match('abc', 0).matched).toBe(true);
      expect(outer.match('abc', 0).consumed).toBe(3);
    });

    it('should return Empty for empty array', () => {
      const result = RegexSequence.create();
      expect(result).toBeInstanceOf(Empty);
    });

    it('should return the single validator for single element', () => {
      const literal = new Literal('x');
      const result = RegexSequence.create(literal);
      expect(result).toBe(literal);
    });
  });
});

