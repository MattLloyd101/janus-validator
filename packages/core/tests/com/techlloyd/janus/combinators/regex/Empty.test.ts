import { Empty } from '@/com/techlloyd/janus/combinators/regex/Empty';
import { DomainType } from '@/com/techlloyd/janus/Domain';
import { RNG } from '@/com/techlloyd/janus/RNG';
import { Generator } from '@/com/techlloyd/janus/Generator';

describe('Empty', () => {
  describe('matching', () => {
    it('should always match at any position', () => {
      const empty = new Empty();
      expect(empty.match('abc', 0).matched).toBe(true);
      expect(empty.match('abc', 1).matched).toBe(true);
      expect(empty.match('abc', 3).matched).toBe(true);
    });

    it('should match on empty string', () => {
      const empty = new Empty();
      expect(empty.match('', 0).matched).toBe(true);
    });

    it('should consume 0 characters', () => {
      const empty = new Empty();
      const result = empty.match('abc', 0);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(0);
    });
  });

  describe('validation', () => {
    it('should validate empty string', () => {
      const empty = new Empty();
      expect(empty.validate('').valid).toBe(true);
    });

    it('should reject non-empty strings', () => {
      const empty = new Empty();
      expect(empty.validate('a').valid).toBe(false);
      expect(empty.validate('abc').valid).toBe(false);
    });

    it('should reject non-strings', () => {
      const empty = new Empty();
      expect(empty.validate(123).valid).toBe(false);
      expect(empty.validate(null).valid).toBe(false);
    });
  });

  describe('generation', () => {
    it('should always generate empty string', () => {
      const empty = new Empty();
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 10; i++) {
        expect(generator.generate(empty.domain)).toBe('');
      }
    });
  });

  describe('domain', () => {
    it('should expose a regex domain with empty source', () => {
      const empty = new Empty();
      expect(empty.domain.type).toBe(DomainType.REGEX_DOMAIN);
      expect(empty.domain.source).toBe('');
    });
  });
});

