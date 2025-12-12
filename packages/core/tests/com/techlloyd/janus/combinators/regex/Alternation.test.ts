import { Alternation, RegexAlternation } from '@/com/techlloyd/janus/combinators/regex/Alternation';
import { Literal } from '@/com/techlloyd/janus/combinators/regex/Literal';
import { Sequence } from '@/com/techlloyd/janus/combinators/regex/Sequence';
import { Empty } from '@/com/techlloyd/janus/combinators/regex/Empty';
import { DomainType } from '@/com/techlloyd/janus/Domain';
import { RNG } from '@/com/techlloyd/janus/RNG';
import { Generator } from '@/com/techlloyd/janus/Generator';

describe('Alternation', () => {
  describe('matching', () => {
    it('should match any of the alternatives', () => {
      const alt = new Alternation(
        new Literal('a'),
        new Literal('b'),
        new Literal('c')
      );
      expect(alt.match('a', 0).matched).toBe(true);
      expect(alt.match('b', 0).matched).toBe(true);
      expect(alt.match('c', 0).matched).toBe(true);
    });

    it('should fail if no alternative matches', () => {
      const alt = new Alternation(
        new Literal('a'),
        new Literal('b'),
        new Literal('c')
      );
      expect(alt.match('x', 0).matched).toBe(false);
    });

    it('should return first matching alternative (greedy left-to-right)', () => {
      const alt = new Alternation(
        new Sequence(new Literal('a'), new Literal('b')),
        new Literal('a')
      );
      // 'ab' should match 'ab', not just 'a'
      const result = alt.match('ab', 0);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(2);
    });

    it('should match at any position', () => {
      const alt = new Alternation(
        new Literal('x'),
        new Literal('y')
      );
      expect(alt.match('ax', 1).matched).toBe(true);
      expect(alt.match('ay', 1).matched).toBe(true);
    });

    it('should work with multi-character sequences', () => {
      const alt = new Alternation(
        new Sequence(new Literal('c'), new Literal('a'), new Literal('t')),
        new Sequence(new Literal('d'), new Literal('o'), new Literal('g')),
        new Sequence(new Literal('b'), new Literal('i'), new Literal('r'), new Literal('d'))
      );
      expect(alt.match('cat', 0).matched).toBe(true);
      expect(alt.match('dog', 0).matched).toBe(true);
      expect(alt.match('bird', 0).matched).toBe(true);
      expect(alt.match('fish', 0).matched).toBe(false);
    });

    it('should handle empty alternatives', () => {
      const alt = new Alternation();
      expect(alt.match('abc', 0).matched).toBe(false);
    });
  });

  describe('validation', () => {
    it('should validate any matching alternative', () => {
      const alt = new Alternation(
        new Literal('x'),
        new Literal('y'),
        new Literal('z')
      );
      expect(alt.validate('x').valid).toBe(true);
      expect(alt.validate('y').valid).toBe(true);
      expect(alt.validate('z').valid).toBe(true);
    });

    it('should reject non-matching values', () => {
      const alt = new Alternation(
        new Literal('x'),
        new Literal('y')
      );
      expect(alt.validate('a').valid).toBe(false);
      expect(alt.validate('xy').valid).toBe(false);
    });

    it('should reject non-strings', () => {
      const alt = new Alternation(new Literal('a'));
      expect(alt.validate(123).valid).toBe(false);
    });
  });

  describe('generation', () => {
    it('should generate one of the alternatives', () => {
      const alt = new Alternation(
        new Literal('a'),
        new Literal('b'),
        new Literal('c')
      );
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(alt.domain);
        expect(['a', 'b', 'c']).toContain(value);
      }
    });

    it('should generate variety over many iterations', () => {
      const alt = new Alternation(
        new Literal('a'),
        new Literal('b'),
        new Literal('c')
      );
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      const generated = new Set<string>();
      for (let i = 0; i < 100; i++) {
        generated.add(generator.generate(alt.domain));
      }
      // Should generate multiple different alternatives
      expect(generated.size).toBeGreaterThan(1);
    });

    it('should select based on RNG value', () => {
      const alt = new Alternation(
        new Literal('x'),
        new Literal('y'),
        new Literal('z')
      );
      // RNG 0 should select first alternative
      expect(new Generator({ random: () => 0.0 }).generate(alt.domain)).toBe('x');
      // RNG close to 1 should select last alternative
      expect(new Generator({ random: () => 0.99 }).generate(alt.domain)).toBe('z');
    });

    it('should generate empty string for empty alternation', () => {
      const alt = new Alternation();
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);
      expect(generator.generate(alt.domain)).toBe('');
    });
  });

  describe('domain', () => {
    it('should join sources with |', () => {
      const alt = new Alternation(
        new Literal('a'),
        new Literal('b'),
        new Literal('c')
      );
      expect(alt.domain.type).toBe(DomainType.REGEX_DOMAIN);
      expect(alt.domain.source).toBe('a|b|c');
    });
  });

  describe('RegexAlternation.create factory', () => {
    it('should flatten nested alternations', () => {
      const inner = new Alternation(new Literal('a'), new Literal('b'));
      const outer = RegexAlternation.create(inner, new Literal('c'));
      
      // Should behave as if it's a flat alternation
      expect(outer.match('a', 0).matched).toBe(true);
      expect(outer.match('b', 0).matched).toBe(true);
      expect(outer.match('c', 0).matched).toBe(true);
    });

    it('should return Empty for empty array', () => {
      const result = RegexAlternation.create();
      expect(result).toBeInstanceOf(Empty);
    });

    it('should return the single validator for single element', () => {
      const literal = new Literal('x');
      const result = RegexAlternation.create(literal);
      expect(result).toBe(literal);
    });
  });
});

