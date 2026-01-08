import { Anchor } from '@/com/techlloyd/janus/combinators/regex/Anchor';
import { DomainType } from '@/com/techlloyd/janus/Domain';
import { RNG } from '@/com/techlloyd/janus/RNG';
import { Generator } from '@/com/techlloyd/janus/Generator';

describe('Anchor', () => {
  describe('start anchor (^)', () => {
    it('should match at position 0', () => {
      const start = new Anchor('start');
      expect(start.match('abc', 0).matched).toBe(true);
    });

    it('should NOT match at other positions', () => {
      const start = new Anchor('start');
      expect(start.match('abc', 1).matched).toBe(false);
      expect(start.match('abc', 2).matched).toBe(false);
    });

    it('should consume 0 characters', () => {
      const start = new Anchor('start');
      const result = start.match('abc', 0);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(0);
    });

    it('should have correct source', () => {
      const start = new Anchor('start');
      expect(start.domain.source).toBe('^');
    });
  });

  describe('end anchor ($)', () => {
    it('should match at end of string', () => {
      const end = new Anchor('end');
      expect(end.match('abc', 3).matched).toBe(true);
    });

    it('should NOT match before end of string', () => {
      const end = new Anchor('end');
      expect(end.match('abc', 0).matched).toBe(false);
      expect(end.match('abc', 2).matched).toBe(false);
    });

    it('should match at position 0 for empty string', () => {
      const end = new Anchor('end');
      expect(end.match('', 0).matched).toBe(true);
    });

    it('should consume 0 characters', () => {
      const end = new Anchor('end');
      const result = end.match('abc', 3);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(0);
    });

    it('should have correct source', () => {
      const end = new Anchor('end');
      expect(end.domain.source).toBe('$');
    });
  });

  // Note: Word boundary (\b, \B) is not supported per ADR-002 (non-portable)

  describe('validation', () => {
    it('start anchor should validate empty string', () => {
      const start = new Anchor('start');
      // ^ matches at position 0, and position 0 is also end of empty string
      expect(start.validate('').valid).toBe(true);
    });

    it('end anchor should validate empty string', () => {
      const end = new Anchor('end');
      expect(end.validate('').valid).toBe(true);
    });

    it('should reject non-empty strings (anchors alone)', () => {
      const start = new Anchor('start');
      const end = new Anchor('end');
      // An anchor alone only matches empty string
      expect(start.validate('a').valid).toBe(false);
      expect(end.validate('a').valid).toBe(false);
    });
  });

  describe('generation', () => {
    it('should always generate empty string', () => {
      const start = new Anchor('start');
      const end = new Anchor('end');
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      expect(generator.generate(start.domain)).toBe('');
      expect(generator.generate(end.domain)).toBe('');
    });
  });

  describe('domain', () => {
    it('should expose a regex domain', () => {
      const start = new Anchor('start');
      expect(start.domain.kind).toBe(DomainType.REGEX);
    });
  });
});

