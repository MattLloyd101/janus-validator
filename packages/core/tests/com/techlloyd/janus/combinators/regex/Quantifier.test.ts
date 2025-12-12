import { Quantifier } from '@/com/techlloyd/janus/combinators/regex/Quantifier';
import { Literal } from '@/com/techlloyd/janus/combinators/regex/Literal';
import { CharClasses } from '@/com/techlloyd/janus/combinators/regex/CharClass';
import { Sequence } from '@/com/techlloyd/janus/combinators/regex/Sequence';
import { DomainType } from '@/com/techlloyd/janus/Domain';
import { RNG } from '@/com/techlloyd/janus/RNG';
import { Generator } from '@/com/techlloyd/janus/Generator';

describe('Quantifier', () => {
  describe('* (zero or more)', () => {
    it('should match zero occurrences', () => {
      const q = Quantifier.zeroOrMore(new Literal('a'));
      const result = q.match('bbb', 0);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(0);
    });

    it('should match multiple occurrences', () => {
      const q = Quantifier.zeroOrMore(new Literal('a'));
      const result = q.match('aaab', 0);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(3);
    });

    it('should be greedy (match as many as possible)', () => {
      const q = Quantifier.zeroOrMore(new Literal('a'));
      const result = q.match('aaaaa', 0);
      expect(result.consumed).toBe(5);
    });

    it('should have correct source', () => {
      const q = Quantifier.zeroOrMore(new Literal('a'));
      expect(q.domain.source).toBe('a*');
    });
  });

  describe('+ (one or more)', () => {
    it('should NOT match zero occurrences', () => {
      const q = Quantifier.oneOrMore(new Literal('a'));
      const result = q.match('bbb', 0);
      expect(result.matched).toBe(false);
    });

    it('should match one occurrence', () => {
      const q = Quantifier.oneOrMore(new Literal('a'));
      const result = q.match('ab', 0);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(1);
    });

    it('should match multiple occurrences', () => {
      const q = Quantifier.oneOrMore(new Literal('a'));
      const result = q.match('aaab', 0);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(3);
    });

    it('should have correct source', () => {
      const q = Quantifier.oneOrMore(new Literal('a'));
      expect(q.domain.source).toBe('a+');
    });
  });

  describe('? (zero or one)', () => {
    it('should match zero occurrences', () => {
      const q = Quantifier.optional(new Literal('a'));
      const result = q.match('bbb', 0);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(0);
    });

    it('should match one occurrence', () => {
      const q = Quantifier.optional(new Literal('a'));
      const result = q.match('ab', 0);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(1);
    });

    it('should only match one even if more available', () => {
      const q = Quantifier.optional(new Literal('a'));
      const result = q.match('aaab', 0);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(1);
    });

    it('should have correct source', () => {
      const q = Quantifier.optional(new Literal('a'));
      expect(q.domain.source).toBe('a?');
    });
  });

  describe('{n} (exactly n)', () => {
    it('should match exactly n occurrences', () => {
      const q = Quantifier.exactly(new Literal('a'), 3);
      const result = q.match('aaab', 0);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(3);
    });

    it('should fail if fewer than n', () => {
      const q = Quantifier.exactly(new Literal('a'), 3);
      const result = q.match('aab', 0);
      expect(result.matched).toBe(false);
    });

    it('should have correct source', () => {
      const q = Quantifier.exactly(new Literal('a'), 5);
      expect(q.domain.source).toBe('a{5}');
    });
  });

  describe('{n,} (at least n)', () => {
    it('should match at least n occurrences', () => {
      const q = Quantifier.atLeast(new Literal('a'), 2);
      expect(q.match('aa', 0).matched).toBe(true);
      expect(q.match('aaa', 0).matched).toBe(true);
      expect(q.match('aaaaa', 0).matched).toBe(true);
    });

    it('should fail if fewer than n', () => {
      const q = Quantifier.atLeast(new Literal('a'), 2);
      expect(q.match('a', 0).matched).toBe(false);
    });

    it('should have correct source', () => {
      const q = Quantifier.atLeast(new Literal('a'), 3);
      expect(q.domain.source).toBe('a{3,}');
    });
  });

  describe('{n,m} (between n and m)', () => {
    it('should match between n and m occurrences', () => {
      const q = Quantifier.between(new Literal('a'), 2, 4);
      expect(q.match('aa', 0).matched).toBe(true);
      expect(q.match('aaa', 0).matched).toBe(true);
      expect(q.match('aaaa', 0).matched).toBe(true);
    });

    it('should fail if fewer than n', () => {
      const q = Quantifier.between(new Literal('a'), 2, 4);
      expect(q.match('a', 0).matched).toBe(false);
    });

    it('should only match up to m', () => {
      const q = Quantifier.between(new Literal('a'), 2, 4);
      const result = q.match('aaaaaa', 0);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(4);
    });

    it('should have correct source', () => {
      const q = Quantifier.between(new Literal('a'), 2, 5);
      expect(q.domain.source).toBe('a{2,5}');
    });
  });

  describe('validation', () => {
    it('should validate matching strings', () => {
      const q = Quantifier.exactly(new Literal('a'), 3);
      expect(q.validate('aaa').valid).toBe(true);
    });

    it('should reject non-matching strings', () => {
      const q = Quantifier.exactly(new Literal('a'), 3);
      expect(q.validate('aa').valid).toBe(false);
      expect(q.validate('aaaa').valid).toBe(false);
    });
  });

  describe('generation', () => {
    it('should generate within min-max range', () => {
      const q = Quantifier.between(new Literal('x'), 2, 5);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(q.domain);
        expect(value.length).toBeGreaterThanOrEqual(2);
        expect(value.length).toBeLessThanOrEqual(5);
        expect(value).toMatch(/^x+$/);
      }
    });

    it('should generate exact count for {n}', () => {
      const q = Quantifier.exactly(new Literal('y'), 4);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 10; i++) {
        expect(generator.generate(q.domain)).toBe('yyyy');
      }
    });

    it('should generate at least 1 for +', () => {
      const q = Quantifier.oneOrMore(new Literal('z'));
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(q.domain);
        expect(value.length).toBeGreaterThanOrEqual(1);
      }
    });

    it('should generate variety for *', () => {
      const q = Quantifier.zeroOrMore(new Literal('a'));
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      const lengths = new Set<number>();
      for (let i = 0; i < 100; i++) {
        lengths.add(generator.generate(q.domain).length);
      }
      // Should generate various lengths including 0
      expect(lengths.size).toBeGreaterThan(3);
    });

    it('should cap unbounded quantifiers', () => {
      const q = Quantifier.zeroOrMore(new Literal('a'));
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(q.domain);
        // Default max is 10
        expect(value.length).toBeLessThanOrEqual(10);
      }
    });
  });

  describe('with complex inner validators', () => {
    it('should work with sequences', () => {
      const seq = new Sequence(new Literal('a'), new Literal('b'));
      const q = Quantifier.exactly(seq, 2);
      
      expect(q.match('abab', 0).matched).toBe(true);
      expect(q.match('abab', 0).consumed).toBe(4);
      expect(q.match('ab', 0).matched).toBe(false);
    });

    it('should work with character classes', () => {
      const q = Quantifier.between(CharClasses.digit(), 3, 5);
      
      expect(q.match('123', 0).matched).toBe(true);
      expect(q.match('12345', 0).matched).toBe(true);
      expect(q.match('12', 0).matched).toBe(false);
    });
  });

  describe('domain', () => {
    it('should expose a regex domain', () => {
      const q = new Quantifier(new Literal('a'), 1, 3);
      expect(q.domain.type).toBe(DomainType.REGEX_DOMAIN);
    });

    it('should wrap multi-char sequences in non-capturing group', () => {
      const seq = new Sequence(new Literal('a'), new Literal('b'));
      const q = Quantifier.oneOrMore(seq);
      expect(q.domain.source).toBe('(?:ab)+');
    });
  });
});

