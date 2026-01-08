import { Literal } from '@/com/techlloyd/janus/combinators/regex/Literal';
import { DomainType } from '@/com/techlloyd/janus/Domain';
import { RNG } from '@/com/techlloyd/janus/RNG';
import { Generator } from '@/com/techlloyd/janus/Generator';

describe('Literal', () => {
  describe('matching', () => {
    it('should match a single character at position 0', () => {
      const literal = new Literal('a');
      const result = literal.match('abc', 0);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(1);
    });

    it('should match a character at any position', () => {
      const literal = new Literal('b');
      const result = literal.match('abc', 1);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(1);
    });

    it('should not match wrong character', () => {
      const literal = new Literal('x');
      const result = literal.match('abc', 0);
      expect(result.matched).toBe(false);
      expect(result.consumed).toBe(0);
    });

    it('should not match past end of string', () => {
      const literal = new Literal('a');
      const result = literal.match('abc', 3);
      expect(result.matched).toBe(false);
      expect(result.consumed).toBe(0);
    });

    it('should match special characters', () => {
      const dot = new Literal('.');
      expect(dot.match('.', 0).matched).toBe(true);

      const star = new Literal('*');
      expect(star.match('*', 0).matched).toBe(true);

      const backslash = new Literal('\\');
      expect(backslash.match('\\', 0).matched).toBe(true);
    });
  });

  describe('validation', () => {
    it('should validate single character string', () => {
      const literal = new Literal('x');
      expect(literal.validate('x').valid).toBe(true);
    });

    it('should reject longer strings', () => {
      const literal = new Literal('x');
      expect(literal.validate('xx').valid).toBe(false);
    });

    it('should reject empty strings', () => {
      const literal = new Literal('x');
      expect(literal.validate('').valid).toBe(false);
    });

    it('should reject non-strings', () => {
      const literal = new Literal('x');
      expect(literal.validate(123).valid).toBe(false);
      expect(literal.validate(null).valid).toBe(false);
    });
  });

  describe('generation', () => {
    it('should always generate the literal character', () => {
      const literal = new Literal('q');
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 10; i++) {
        expect(generator.generate(literal.domain)).toBe('q');
      }
    });
  });

  describe('domain', () => {
    it('should expose a regex domain', () => {
      const literal = new Literal('a');
      expect(literal.domain.kind).toBe(DomainType.REGEX);
      expect(literal.domain.source).toBe('a');
    });

    it('should escape special regex characters in source', () => {
      const dot = new Literal('.');
      expect(dot.domain.source).toBe('\\.');

      const star = new Literal('*');
      expect(star.domain.source).toBe('\\*');
    });
  });
});

