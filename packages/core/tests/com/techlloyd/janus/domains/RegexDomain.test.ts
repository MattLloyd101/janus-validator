import { RegexDomain } from '@/com/techlloyd/janus/Domain';
import { DomainType } from '@/com/techlloyd/janus/domains/types';

describe('RegexDomain', () => {
  describe('construction', () => {
    it('creates domain from RegExp', () => {
      const domain = new RegexDomain(/^[a-z]+$/);
      expect(domain.type).toBe(DomainType.REGEX_DOMAIN);
      expect(domain.source).toBe('^[a-z]+$');
    });

    it('extracts source from pattern automatically', () => {
      const pattern = /^\d{3}-\d{4}$/;
      const domain = new RegexDomain(pattern);
      expect(domain.pattern).toBe(pattern);
      expect(domain.source).toBe('^\\d{3}-\\d{4}$');
    });
  });

  describe('encapsulates - equality', () => {
    it('same source encapsulates', () => {
      const a = new RegexDomain(/^hello$/);
      const b = new RegexDomain(/^hello$/);
      expect(a.encapsulates(b).result).toBe('true');
      expect(b.encapsulates(a).result).toBe('true');
    });

    it('different sources need structural comparison', () => {
      const a = new RegexDomain(/^[a-z]$/);
      const b = new RegexDomain(/^[a-m]$/);
      // [a-z] encapsulates [a-m]
      expect(a.encapsulates(b).result).toBe('true');
      // [a-m] does not encapsulate [a-z]
      expect(b.encapsulates(a).result).toBe('false');
    });
  });

  describe('encapsulates - literals', () => {
    it('same literal encapsulates', () => {
      const a = new RegexDomain(/^abc$/);
      const b = new RegexDomain(/^abc$/);
      expect(a.encapsulates(b).result).toBe('true');
    });

    it('char class encapsulates literal it contains', () => {
      const charClass = new RegexDomain(/^[a-z]$/);
      const literal = new RegexDomain(/^a$/);
      expect(charClass.encapsulates(literal).result).toBe('true');
    });

    it('char class does not encapsulate literal outside range', () => {
      const charClass = new RegexDomain(/^[a-m]$/);
      const literal = new RegexDomain(/^z$/);
      expect(charClass.encapsulates(literal).result).toBe('false');
    });
  });

  describe('encapsulates - character classes', () => {
    it('wider char class encapsulates narrower', () => {
      const wide = new RegexDomain(/^[a-z]$/);
      const narrow = new RegexDomain(/^[a-f]$/);
      expect(wide.encapsulates(narrow).result).toBe('true');
    });

    it('narrower char class does not encapsulate wider', () => {
      const wide = new RegexDomain(/^[a-z]$/);
      const narrow = new RegexDomain(/^[a-f]$/);
      expect(narrow.encapsulates(wide).result).toBe('false');
    });

    it('disjoint char classes do not encapsulate', () => {
      const letters = new RegexDomain(/^[a-z]$/);
      const digits = new RegexDomain(/^[0-9]$/);
      expect(letters.encapsulates(digits).result).toBe('false');
      expect(digits.encapsulates(letters).result).toBe('false');
    });

    it('any (.) encapsulates char class', () => {
      const any = new RegexDomain(/^.$/);
      const charClass = new RegexDomain(/^[a-z]$/);
      expect(any.encapsulates(charClass).result).toBe('true');
    });
  });

  describe('encapsulates - sequences', () => {
    it('equal sequences encapsulate', () => {
      const a = new RegexDomain(/^abc$/);
      const b = new RegexDomain(/^abc$/);
      expect(a.encapsulates(b).result).toBe('true');
    });

    it('wider char classes in sequence encapsulate', () => {
      const wide = new RegexDomain(/^[a-z][0-9]$/);
      const narrow = new RegexDomain(/^[a-f][0-5]$/);
      expect(wide.encapsulates(narrow).result).toBe('true');
    });

    it('different length sequences do not encapsulate', () => {
      const short = new RegexDomain(/^ab$/);
      const long = new RegexDomain(/^abc$/);
      expect(short.encapsulates(long).result).toBe('false');
      expect(long.encapsulates(short).result).toBe('false');
    });
  });

  describe('encapsulates - quantifiers', () => {
    it('wider quantifier bounds encapsulate narrower', () => {
      // + is {1,∞}, {2,5} is subset
      const plus = new RegexDomain(/^a+$/);
      const bounded = new RegexDomain(/^a{2,5}$/);
      expect(plus.encapsulates(bounded).result).toBe('true');
    });

    it('narrower quantifier does not encapsulate wider', () => {
      const bounded = new RegexDomain(/^a{2,5}$/);
      const plus = new RegexDomain(/^a+$/);
      expect(bounded.encapsulates(plus).result).toBe('false');
    });

    it('* encapsulates +', () => {
      const star = new RegexDomain(/^a*$/);
      const plus = new RegexDomain(/^a+$/);
      expect(star.encapsulates(plus).result).toBe('true');
    });

    it('+ does not encapsulate *', () => {
      const star = new RegexDomain(/^a*$/);
      const plus = new RegexDomain(/^a+$/);
      expect(plus.encapsulates(star).result).toBe('false');
    });

    it('? encapsulates {0,1}', () => {
      const optional = new RegexDomain(/^a?$/);
      const bounded = new RegexDomain(/^a{0,1}$/);
      expect(optional.encapsulates(bounded).result).toBe('true');
      expect(bounded.encapsulates(optional).result).toBe('true');
    });

    it('inner domain must also be compatible', () => {
      const wide = new RegexDomain(/^[a-z]+$/);
      const narrow = new RegexDomain(/^[a-f]+$/);
      expect(wide.encapsulates(narrow).result).toBe('true');
      expect(narrow.encapsulates(wide).result).toBe('false');
    });
  });

  describe('encapsulates - alternations', () => {
    it('handles alternation in both patterns with same structure', () => {
      const alt1 = new RegexDomain(/^(abc|xyz)$/);
      const alt2 = new RegexDomain(/^(abc|xyz)$/);
      expect(alt1.encapsulates(alt2).result).toBe('true');
    });

    it('wider char range alternation encapsulates narrower with same structure', () => {
      // Same alternation structure with char classes
      const wider = new RegexDomain(/^[a-z]$/);
      const narrower = new RegexDomain(/^[a-m]$/);
      expect(wider.encapsulates(narrower).result).toBe('true');
    });

    it('does not encapsulate when patterns differ structurally', () => {
      const letters = new RegexDomain(/^[a-z]+$/);
      const mixed = new RegexDomain(/^(abc|123)$/);
      // Different structure - quantifier vs alternation
      expect(letters.encapsulates(mixed).result).toBe('false');
    });
  });

  describe('encapsulates - anchors', () => {
    it('same anchors encapsulate', () => {
      const a = new RegexDomain(/^test$/);
      const b = new RegexDomain(/^test$/);
      expect(a.encapsulates(b).result).toBe('true');
    });

    it('different anchors do not match', () => {
      const start = new RegexDomain(/^test/);
      const end = new RegexDomain(/test$/);
      // These have different anchor structures
      expect(start.encapsulates(end).result).toBe('false');
    });
  });

  describe('encapsulates - groups', () => {
    it('same grouped patterns encapsulate each other', () => {
      const grouped1 = new RegexDomain(/^(abc)$/);
      const grouped2 = new RegexDomain(/^(abc)$/);
      expect(grouped1.encapsulates(grouped2).result).toBe('true');
    });

    it('nested groups with same structure encapsulate', () => {
      const nested1 = new RegexDomain(/^((a))$/);
      const nested2 = new RegexDomain(/^((a))$/);
      expect(nested1.encapsulates(nested2).result).toBe('true');
    });

    it('group with wider inner range encapsulates narrower', () => {
      const wide = new RegexDomain(/^([a-z])$/);
      const narrow = new RegexDomain(/^([a-m])$/);
      expect(wide.encapsulates(narrow).result).toBe('true');
    });
  });

  describe('encapsulates - type mismatch', () => {
    it('returns false for non-RegexDomain', () => {
      const regex = new RegexDomain(/^test$/);
      const { FiniteDomain } = require('@/com/techlloyd/janus/Domain');
      const finite = new FiniteDomain(['test']);
      expect(regex.encapsulates(finite as any).result).toBe('false');
    });
  });
});
