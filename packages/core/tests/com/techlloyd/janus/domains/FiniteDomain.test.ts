import { FiniteDomain } from '@/com/techlloyd/janus/Domain';
import { DomainType } from '@/com/techlloyd/janus/domains/types';

describe('FiniteDomain', () => {
  describe('construction', () => {
    it('creates domain with number values', () => {
      const domain = new FiniteDomain([1, 2, 3]);
      expect(domain.type).toBe(DomainType.FINITE_DOMAIN);
      expect(domain.values).toEqual([1, 2, 3]);
    });

    it('creates domain with string values', () => {
      const domain = new FiniteDomain(['a', 'b', 'c']);
      expect(domain.values).toEqual(['a', 'b', 'c']);
    });

    it('creates domain with boolean values', () => {
      const domain = new FiniteDomain([true, false]);
      expect(domain.values).toEqual([true, false]);
    });

    it('creates domain with single value', () => {
      const domain = new FiniteDomain([42]);
      expect(domain.values).toEqual([42]);
    });

    it('creates domain with null/undefined', () => {
      const domain = new FiniteDomain([null, undefined]);
      expect(domain.values).toContain(null);
      expect(domain.values).toContain(undefined);
    });
  });

  describe('encapsulates', () => {
    it('superset encapsulates subset', () => {
      const superset = new FiniteDomain([1, 2, 3, 4, 5]);
      const subset = new FiniteDomain([2, 3]);
      expect(superset.encapsulates(subset).result).toBe('true');
    });

    it('subset does not encapsulate superset', () => {
      const superset = new FiniteDomain([1, 2, 3, 4, 5]);
      const subset = new FiniteDomain([2, 3]);
      expect(subset.encapsulates(superset).result).toBe('false');
    });

    it('equal sets encapsulate each other', () => {
      const a = new FiniteDomain([1, 2, 3]);
      const b = new FiniteDomain([1, 2, 3]);
      expect(a.encapsulates(b).result).toBe('true');
      expect(b.encapsulates(a).result).toBe('true');
    });

    it('disjoint sets do not encapsulate', () => {
      const a = new FiniteDomain([1, 2, 3]);
      const b = new FiniteDomain([4, 5, 6]);
      expect(a.encapsulates(b).result).toBe('false');
      expect(b.encapsulates(a).result).toBe('false');
    });

    it('empty domain is encapsulated by any domain', () => {
      const empty = new FiniteDomain<number>([]);
      const nonEmpty = new FiniteDomain([1, 2, 3]);
      expect(nonEmpty.encapsulates(empty).result).toBe('true');
    });

    it('handles string equality correctly', () => {
      const a = new FiniteDomain(['hello', 'world']);
      const b = new FiniteDomain(['hello']);
      expect(a.encapsulates(b).result).toBe('true');
      expect(b.encapsulates(a).result).toBe('false');
    });

    it('partial overlap does not encapsulate', () => {
      const a = new FiniteDomain([1, 2, 3]);
      const b = new FiniteDomain([2, 3, 4]);
      expect(a.encapsulates(b).result).toBe('false');
      expect(b.encapsulates(a).result).toBe('false');
    });
  });
});

