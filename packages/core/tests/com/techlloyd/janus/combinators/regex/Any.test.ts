import { Any } from '@/com/techlloyd/janus/combinators/regex/Any';
import { DomainType } from '@/com/techlloyd/janus/Domain';
import { RNG } from '@/com/techlloyd/janus/RNG';

describe('Any', () => {
  describe('matching', () => {
    it('should match any printable character', () => {
      const any = new Any();
      expect(any.match('a', 0).matched).toBe(true);
      expect(any.match('Z', 0).matched).toBe(true);
      expect(any.match('5', 0).matched).toBe(true);
      expect(any.match('!', 0).matched).toBe(true);
      expect(any.match(' ', 0).matched).toBe(true);
    });

    it('should NOT match newline', () => {
      const any = new Any();
      expect(any.match('\n', 0).matched).toBe(false);
    });

    it('should consume exactly 1 character', () => {
      const any = new Any();
      const result = any.match('abc', 0);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(1);
    });

    it('should match at any position', () => {
      const any = new Any();
      expect(any.match('abc', 1).matched).toBe(true);
      expect(any.match('abc', 2).matched).toBe(true);
    });

    it('should not match past end of string', () => {
      const any = new Any();
      expect(any.match('a', 1).matched).toBe(false);
    });
  });

  describe('validation', () => {
    it('should validate single character strings', () => {
      const any = new Any();
      expect(any.validate('x').valid).toBe(true);
      expect(any.validate('!').valid).toBe(true);
    });

    it('should reject multi-character strings', () => {
      const any = new Any();
      expect(any.validate('ab').valid).toBe(false);
      expect(any.validate('abc').valid).toBe(false);
    });

    it('should reject empty string', () => {
      const any = new Any();
      expect(any.validate('').valid).toBe(false);
    });

    it('should reject newline', () => {
      const any = new Any();
      expect(any.validate('\n').valid).toBe(false);
    });

    it('should reject non-strings', () => {
      const any = new Any();
      expect(any.validate(123).valid).toBe(false);
      expect(any.validate(null).valid).toBe(false);
    });
  });

  describe('generation', () => {
    it('should generate printable ASCII characters', () => {
      const any = new Any();
      const rng: RNG = { random: () => Math.random() };

      for (let i = 0; i < 100; i++) {
        const value = any.generate(rng);
        expect(value.length).toBe(1);
        const code = value.charCodeAt(0);
        expect(code).toBeGreaterThanOrEqual(32);
        expect(code).toBeLessThanOrEqual(126);
      }
    });

    it('should generate variety of characters', () => {
      const any = new Any();
      const rng: RNG = { random: () => Math.random() };

      const generated = new Set<string>();
      for (let i = 0; i < 200; i++) {
        generated.add(any.generate(rng));
      }
      // Should generate many different characters
      expect(generated.size).toBeGreaterThan(20);
    });
  });

  describe('domain', () => {
    it('should expose a regex domain with "." source', () => {
      const any = new Any();
      expect(any.domain.type).toBe(DomainType.REGEX_DOMAIN);
      expect(any.domain.source).toBe('.');
    });
  });
});

