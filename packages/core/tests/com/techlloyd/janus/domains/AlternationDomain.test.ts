import { AlternationDomain, FiniteDomain, ContiguousDomain, ContiguousType } from '@/com/techlloyd/janus/Domain';
import { DomainType } from '@/com/techlloyd/janus/domains/types';

describe('AlternationDomain', () => {
  describe('construction', () => {
    it('creates domain with multiple alternatives', () => {
      const alt = new AlternationDomain([
        new FiniteDomain([1, 2]),
        new FiniteDomain([3, 4]),
      ]);
      expect(alt.type).toBe(DomainType.ALTERNATION_DOMAIN);
      expect(alt.alternatives).toHaveLength(2);
    });
  });

  describe('encapsulates', () => {
    it('alternation encapsulates if any alternative encapsulates', () => {
      const alt = new AlternationDomain([
        new ContiguousDomain(ContiguousType.INTEGER, 0, 10),
        new ContiguousDomain(ContiguousType.INTEGER, 100, 200),
      ]);
      const target = new ContiguousDomain(ContiguousType.INTEGER, 2, 5);

      expect(alt.encapsulates(target).result).toBe('true');
    });

    it('alternation returns unknown if no alternative encapsulates', () => {
      const alt = new AlternationDomain([
        new ContiguousDomain(ContiguousType.INTEGER, 0, 10),
        new ContiguousDomain(ContiguousType.INTEGER, 100, 200),
      ]);
      const target = new ContiguousDomain(ContiguousType.INTEGER, 50, 60);

      // Returns unknown when none of the branches encapsulate
      // (we can't definitively say it's false without full set analysis)
      expect(alt.encapsulates(target).result).toBe('unknown');
    });

    it('alternation encapsulates another alternation if all alternatives covered', () => {
      const outer = new AlternationDomain([
        new ContiguousDomain(ContiguousType.INTEGER, 0, 100),
        new ContiguousDomain(ContiguousType.INTEGER, 200, 300),
      ]);
      const inner = new AlternationDomain([
        new ContiguousDomain(ContiguousType.INTEGER, 10, 20),
        new ContiguousDomain(ContiguousType.INTEGER, 210, 220),
      ]);

      expect(outer.encapsulates(inner).result).toBe('true');
    });

    it('returns unknown when any inner alternative not covered', () => {
      const outer = new AlternationDomain([
        new ContiguousDomain(ContiguousType.INTEGER, 0, 100),
      ]);
      const inner = new AlternationDomain([
        new ContiguousDomain(ContiguousType.INTEGER, 10, 20),
        new ContiguousDomain(ContiguousType.INTEGER, 500, 600), // not covered
      ]);

      // One alternative is covered, one is not - returns unknown
      // (the inner alternation as a whole might still be encapsulated)
      expect(outer.encapsulates(inner).result).toBe('unknown');
    });

    it('handles mixed domain types in alternatives', () => {
      const alt = new AlternationDomain([
        new FiniteDomain([1, 2, 3]),
        new ContiguousDomain(ContiguousType.INTEGER, 100, 200),
      ]);
      
      const finite = new FiniteDomain([1, 2]);
      expect(alt.encapsulates(finite).result).toBe('true');
      
      const contiguous = new ContiguousDomain(ContiguousType.INTEGER, 150, 160);
      expect(alt.encapsulates(contiguous).result).toBe('true');
    });
  });
});
