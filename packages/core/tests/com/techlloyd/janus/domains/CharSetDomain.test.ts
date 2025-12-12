import { CharSetDomain, charRange } from '@/com/techlloyd/janus/Domain';
import { DomainType } from '@/com/techlloyd/janus/domains/types';

describe('CharSetDomain', () => {
  describe('construction', () => {
    it('creates domain with single range', () => {
      const domain = new CharSetDomain(1, 10, [charRange('a', 'z')]);
      expect(domain.type).toBe(DomainType.CHARSET_DOMAIN);
      expect(domain.ranges).toHaveLength(1);
      expect(domain.minLength).toBe(1);
      expect(domain.maxLength).toBe(10);
    });

    it('creates domain with multiple ranges', () => {
      const domain = new CharSetDomain(1, 5, [
        charRange('a', 'z'),
        charRange('A', 'Z'),
        charRange('0', '9'),
      ]);
      expect(domain.ranges.length).toBeGreaterThanOrEqual(3);
    });

    it('normalizes overlapping ranges', () => {
      const domain = new CharSetDomain(1, 10, [
        charRange('a', 'm'),
        charRange('k', 'z'),
      ]);
      // Should be merged into [a-z]
      expect(domain.ranges).toHaveLength(1);
      expect(domain.ranges[0].min).toBe('a'.codePointAt(0));
      expect(domain.ranges[0].max).toBe('z'.codePointAt(0));
    });

    it('calculates size correctly', () => {
      const domain = new CharSetDomain(1, 5, [charRange('a', 'z')]);
      expect(domain.size).toBe(26); // a-z = 26 chars
    });
  });

  describe('encapsulates', () => {
    it('wider range encapsulates narrower range', () => {
      const wide = new CharSetDomain(1, 10, [charRange('a', 'z')]);
      const narrow = new CharSetDomain(1, 10, [charRange('a', 'm')]);
      expect(wide.encapsulates(narrow).result).toBe('true');
    });

    it('narrower range does not encapsulate wider range', () => {
      const wide = new CharSetDomain(1, 10, [charRange('a', 'z')]);
      const narrow = new CharSetDomain(1, 10, [charRange('a', 'm')]);
      expect(narrow.encapsulates(wide).result).toBe('false');
    });

    it('equal ranges encapsulate each other', () => {
      const a = new CharSetDomain(1, 10, [charRange('0', '9')]);
      const b = new CharSetDomain(1, 10, [charRange('0', '9')]);
      expect(a.encapsulates(b).result).toBe('true');
      expect(b.encapsulates(a).result).toBe('true');
    });

    it('non-overlapping ranges do not encapsulate', () => {
      const letters = new CharSetDomain(1, 5, [charRange('a', 'z')]);
      const digits = new CharSetDomain(1, 5, [charRange('0', '9')]);
      expect(letters.encapsulates(digits).result).toBe('false');
      expect(digits.encapsulates(letters).result).toBe('false');
    });

    it('multi-range domain can encapsulate single-range domain', () => {
      const alphanumeric = new CharSetDomain(1, 10, [
        charRange('a', 'z'),
        charRange('A', 'Z'),
        charRange('0', '9'),
      ]);
      const lowercase = new CharSetDomain(1, 10, [charRange('a', 'z')]);
      expect(alphanumeric.encapsulates(lowercase).result).toBe('true');
    });

    it('length bounds affect encapsulation', () => {
      const longRange = new CharSetDomain(1, 100, [charRange('a', 'z')]);
      const shortRange = new CharSetDomain(1, 10, [charRange('a', 'z')]);
      
      // long encapsulates short (short's max is within long's)
      expect(longRange.encapsulates(shortRange).result).toBe('true');
      // short does not encapsulate long (long's max exceeds short's)
      expect(shortRange.encapsulates(longRange).result).toBe('false');
    });

    it('returns type mismatch for non-CharSetDomain', () => {
      const charSet = new CharSetDomain(1, 10, [charRange('a', 'z')]);
      const { FiniteDomain } = require('@/com/techlloyd/janus/Domain');
      const finite = new FiniteDomain(['a', 'b', 'c']);
      expect(charSet.encapsulates(finite as any).result).toBe('false');
    });
  });
});
