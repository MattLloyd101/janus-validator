import { QuantifierDomain, FiniteDomain, ContiguousDomain, ContiguousType } from '@/com/techlloyd/janus/Domain';
import { DomainType } from '@/com/techlloyd/janus/domains/types';

describe('QuantifierDomain', () => {
  describe('construction', () => {
    it('creates domain with min/max bounds', () => {
      const domain = new QuantifierDomain(new FiniteDomain([1, 2]), 0, 10);
      expect(domain.type).toBe(DomainType.QUANTIFIER_DOMAIN);
      expect(domain.min).toBe(0);
      expect(domain.max).toBe(10);
    });

    it('allows unbounded max (Infinity)', () => {
      const domain = new QuantifierDomain(new FiniteDomain([1]), 1, Infinity);
      expect(domain.max).toBe(Infinity);
    });

    it('allows zero minimum', () => {
      const domain = new QuantifierDomain(new FiniteDomain(['a']), 0, 5);
      expect(domain.min).toBe(0);
    });

    it('allows exact count (min === max)', () => {
      const domain = new QuantifierDomain(new FiniteDomain([true]), 3, 3);
      expect(domain.min).toBe(domain.max);
    });
  });

  describe('encapsulates', () => {
    it('wider bounds encapsulate narrower bounds', () => {
      const wide = new QuantifierDomain(new FiniteDomain([1, 2, 3]), 0, 100);
      const narrow = new QuantifierDomain(new FiniteDomain([1, 2]), 5, 50);

      expect(wide.encapsulates(narrow).result).toBe('true');
    });

    it('narrower bounds do not encapsulate wider bounds', () => {
      const wide = new QuantifierDomain(new FiniteDomain([1, 2]), 0, 100);
      const narrow = new QuantifierDomain(new FiniteDomain([1, 2]), 5, 50);

      expect(narrow.encapsulates(wide).result).toBe('false');
    });

    it('equal bounds encapsulate each other', () => {
      const a = new QuantifierDomain(new FiniteDomain([1]), 2, 10);
      const b = new QuantifierDomain(new FiniteDomain([1]), 2, 10);

      expect(a.encapsulates(b).result).toBe('true');
      expect(b.encapsulates(a).result).toBe('true');
    });

    it('considers inner domain encapsulation', () => {
      const wide = new QuantifierDomain(
        new ContiguousDomain(ContiguousType.INTEGER, 0, 100),
        0, 10
      );
      const narrow = new QuantifierDomain(
        new ContiguousDomain(ContiguousType.INTEGER, 10, 50),
        0, 10
      );

      expect(wide.encapsulates(narrow).result).toBe('true');
    });

    it('fails when inner domain does not encapsulate', () => {
      const dom1 = new QuantifierDomain(
        new ContiguousDomain(ContiguousType.INTEGER, 0, 50),
        0, 10
      );
      const dom2 = new QuantifierDomain(
        new ContiguousDomain(ContiguousType.INTEGER, 0, 100),
        0, 10
      );

      expect(dom1.encapsulates(dom2).result).toBe('false');
    });

    describe('boundary conditions', () => {
      it('min=0 encapsulates min=0', () => {
        const a = new QuantifierDomain(new FiniteDomain([1]), 0, 10);
        const b = new QuantifierDomain(new FiniteDomain([1]), 0, 5);
        expect(a.encapsulates(b).result).toBe('true');
      });

      it('min=1 does not encapsulate min=0', () => {
        const a = new QuantifierDomain(new FiniteDomain([1]), 1, 10);
        const b = new QuantifierDomain(new FiniteDomain([1]), 0, 5);
        expect(a.encapsulates(b).result).toBe('false');
      });

      it('max=Infinity encapsulates any finite max', () => {
        const unbounded = new QuantifierDomain(new FiniteDomain([1]), 0, Infinity);
        const bounded = new QuantifierDomain(new FiniteDomain([1]), 0, 1000000);
        expect(unbounded.encapsulates(bounded).result).toBe('true');
      });

      it('finite max does not encapsulate Infinity', () => {
        const bounded = new QuantifierDomain(new FiniteDomain([1]), 0, 100);
        const unbounded = new QuantifierDomain(new FiniteDomain([1]), 0, Infinity);
        expect(bounded.encapsulates(unbounded).result).toBe('false');
      });
    });
  });
});
