import { StringDomain, FiniteDomain } from '@/com/techlloyd/janus/Domain';
import { DomainType } from '@/com/techlloyd/janus/domains/types';

describe('StringDomain', () => {
  describe('construction', () => {
    it('creates domain with length bounds', () => {
      const domain = new StringDomain(5, 100);
      expect(domain.type).toBe(DomainType.STRING_DOMAIN);
      expect(domain.minLength).toBe(5);
      expect(domain.maxLength).toBe(100);
    });

    it('allows zero minimum length', () => {
      const domain = new StringDomain(0, 50);
      expect(domain.minLength).toBe(0);
    });

    it('allows unbounded max length', () => {
      const domain = new StringDomain(1, Infinity);
      expect(domain.maxLength).toBe(Infinity);
    });

    it('accepts parts for compound strings', () => {
      const parts = ['prefix'];
      const domain = new StringDomain(6, 6, { _parts: parts });
      expect(domain._parts).toEqual(parts);
    });

    it('allows no explicit length bounds', () => {
      const domain = new StringDomain();
      expect(domain.minLength).toBeUndefined();
      expect(domain.maxLength).toBeUndefined();
    });
  });

  describe('encapsulates', () => {
    describe('length bounds', () => {
      it('wider length encapsulates narrower length', () => {
        const wide = new StringDomain(0, 100);
        const narrow = new StringDomain(10, 50);
        expect(wide.encapsulates(narrow).result).toBe('true');
      });

      it('narrower length does not encapsulate wider', () => {
        const wide = new StringDomain(0, 100);
        const narrow = new StringDomain(10, 50);
        expect(narrow.encapsulates(wide).result).toBe('false');
      });

      it('equal lengths encapsulate each other', () => {
        const a = new StringDomain(5, 50);
        const b = new StringDomain(5, 50);
        expect(a.encapsulates(b).result).toBe('true');
        expect(b.encapsulates(a).result).toBe('true');
      });

      it('handles exact length constraints', () => {
        const exact5 = new StringDomain(5, 5);
        const range = new StringDomain(1, 10);
        expect(range.encapsulates(exact5).result).toBe('true');
        expect(exact5.encapsulates(range).result).toBe('false');
      });

      it('undefined bounds treated as 0 to infinity', () => {
        const unbounded = new StringDomain();
        const bounded = new StringDomain(10, 50);
        expect(unbounded.encapsulates(bounded).result).toBe('true');
      });
    });

    describe('compound parts', () => {
      it('equal literal parts encapsulate each other', () => {
        const a = new StringDomain(6, 6, { _parts: ['prefix'] });
        const b = new StringDomain(6, 6, { _parts: ['prefix'] });
        expect(a.encapsulates(b).result).toBe('true');
      });

      it('different literal parts do not encapsulate', () => {
        const a = new StringDomain(3, 3, { _parts: ['abc'] });
        const b = new StringDomain(3, 3, { _parts: ['xyz'] });
        expect(a.encapsulates(b).result).toBe('false');
      });

      it('different number of parts returns unknown', () => {
        const onePart = new StringDomain(1, 10, { _parts: ['a'] });
        const twoParts = new StringDomain(2, 10, { _parts: ['a', 'b'] });
        expect(onePart.encapsulates(twoParts).result).toBe('unknown');
      });

      it('domain parts can encapsulate', () => {
        const wideInner = new FiniteDomain(['a', 'b', 'c']);
        const narrowInner = new FiniteDomain(['a', 'b']);
        const wide = new StringDomain(1, 1, { _parts: [wideInner] });
        const narrow = new StringDomain(1, 1, { _parts: [narrowInner] });
        expect(wide.encapsulates(narrow).result).toBe('true');
      });
    });
  });
});
