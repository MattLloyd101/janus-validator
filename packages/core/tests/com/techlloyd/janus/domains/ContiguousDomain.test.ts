import { ContiguousDomain, ContiguousType } from '@/com/techlloyd/janus/Domain';
import { DomainType } from '@/com/techlloyd/janus/domains/types';

describe('ContiguousDomain', () => {
  describe('construction', () => {
    it('creates integer domain', () => {
      const domain = new ContiguousDomain(ContiguousType.INTEGER, 0, 100);
      expect(domain.type).toBe(DomainType.CONTIGUOUS_DOMAIN);
      expect(domain.contiguousType).toBe(ContiguousType.INTEGER);
      expect(domain.min).toBe(0);
      expect(domain.max).toBe(100);
    });

    it('creates float domain', () => {
      const domain = new ContiguousDomain(ContiguousType.FLOAT, -1.5, 1.5);
      expect(domain.contiguousType).toBe(ContiguousType.FLOAT);
      expect(domain.min).toBe(-1.5);
      expect(domain.max).toBe(1.5);
    });

    it('allows negative ranges', () => {
      const domain = new ContiguousDomain(ContiguousType.INTEGER, -100, -50);
      expect(domain.min).toBe(-100);
      expect(domain.max).toBe(-50);
    });

    it('allows single point range', () => {
      const domain = new ContiguousDomain(ContiguousType.INTEGER, 42, 42);
      expect(domain.min).toBe(domain.max);
    });
  });

  describe('encapsulates', () => {
    it('wider range encapsulates narrower range', () => {
      const wide = new ContiguousDomain(ContiguousType.INTEGER, 0, 100);
      const narrow = new ContiguousDomain(ContiguousType.INTEGER, 10, 50);
      expect(wide.encapsulates(narrow).result).toBe('true');
    });

    it('narrower range does not encapsulate wider range', () => {
      const wide = new ContiguousDomain(ContiguousType.INTEGER, 0, 100);
      const narrow = new ContiguousDomain(ContiguousType.INTEGER, 10, 50);
      expect(narrow.encapsulates(wide).result).toBe('false');
    });

    it('equal ranges encapsulate each other', () => {
      const a = new ContiguousDomain(ContiguousType.INTEGER, 0, 100);
      const b = new ContiguousDomain(ContiguousType.INTEGER, 0, 100);
      expect(a.encapsulates(b).result).toBe('true');
      expect(b.encapsulates(a).result).toBe('true');
    });

    it('non-overlapping ranges do not encapsulate', () => {
      const a = new ContiguousDomain(ContiguousType.INTEGER, 0, 10);
      const b = new ContiguousDomain(ContiguousType.INTEGER, 20, 30);
      expect(a.encapsulates(b).result).toBe('false');
      expect(b.encapsulates(a).result).toBe('false');
    });

    it('partial overlap does not encapsulate', () => {
      const a = new ContiguousDomain(ContiguousType.INTEGER, 0, 50);
      const b = new ContiguousDomain(ContiguousType.INTEGER, 25, 75);
      expect(a.encapsulates(b).result).toBe('false');
      expect(b.encapsulates(a).result).toBe('false');
    });

    it('works with negative ranges', () => {
      const wide = new ContiguousDomain(ContiguousType.INTEGER, -100, 100);
      const narrow = new ContiguousDomain(ContiguousType.INTEGER, -50, 50);
      expect(wide.encapsulates(narrow).result).toBe('true');
    });

    it('works with float domains', () => {
      const wide = new ContiguousDomain(ContiguousType.FLOAT, 0.0, 1.0);
      const narrow = new ContiguousDomain(ContiguousType.FLOAT, 0.25, 0.75);
      expect(wide.encapsulates(narrow).result).toBe('true');
    });

    it('type mismatch returns false', () => {
      const int = new ContiguousDomain(ContiguousType.INTEGER, 0, 100);
      const float = new ContiguousDomain(ContiguousType.FLOAT, 0, 100);
      expect(int.encapsulates(float).result).toBe('false');
    });

    describe('boundary conditions', () => {
      it('handles min boundary exactly', () => {
        const outer = new ContiguousDomain(ContiguousType.INTEGER, 0, 100);
        const inner = new ContiguousDomain(ContiguousType.INTEGER, 0, 50);
        expect(outer.encapsulates(inner).result).toBe('true');
      });

      it('handles max boundary exactly', () => {
        const outer = new ContiguousDomain(ContiguousType.INTEGER, 0, 100);
        const inner = new ContiguousDomain(ContiguousType.INTEGER, 50, 100);
        expect(outer.encapsulates(inner).result).toBe('true');
      });

      it('fails when inner min is below outer min', () => {
        const outer = new ContiguousDomain(ContiguousType.INTEGER, 10, 100);
        const inner = new ContiguousDomain(ContiguousType.INTEGER, 5, 50);
        expect(outer.encapsulates(inner).result).toBe('false');
      });

      it('fails when inner max is above outer max', () => {
        const outer = new ContiguousDomain(ContiguousType.INTEGER, 0, 100);
        const inner = new ContiguousDomain(ContiguousType.INTEGER, 50, 150);
        expect(outer.encapsulates(inner).result).toBe('false');
      });
    });
  });
});
