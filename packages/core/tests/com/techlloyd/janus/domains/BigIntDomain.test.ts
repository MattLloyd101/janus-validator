import { BigIntDomain } from '@/com/techlloyd/janus/Domain';
import { DomainType } from '@/com/techlloyd/janus/domains/types';

describe('BigIntDomain', () => {
  describe('construction', () => {
    it('creates domain with bigint bounds', () => {
      const domain = new BigIntDomain(0n, 1000n);
      expect(domain.type).toBe(DomainType.BIGINT_DOMAIN);
      expect(domain.min).toBe(0n);
      expect(domain.max).toBe(1000n);
    });

    it('handles negative bigints', () => {
      const domain = new BigIntDomain(-1000n, -100n);
      expect(domain.min).toBe(-1000n);
      expect(domain.max).toBe(-100n);
    });

    it('handles very large bigints', () => {
      const huge = 10n ** 100n; // 10^100
      const domain = new BigIntDomain(0n, huge);
      expect(domain.max).toBe(huge);
    });

    it('allows single value (min === max)', () => {
      const domain = new BigIntDomain(42n, 42n);
      expect(domain.min).toBe(domain.max);
    });
  });

  describe('encapsulates', () => {
    it('wider range encapsulates narrower range', () => {
      const wide = new BigIntDomain(0n, 1000n);
      const narrow = new BigIntDomain(100n, 500n);
      expect(wide.encapsulates(narrow).result).toBe('true');
    });

    it('narrower range does not encapsulate wider', () => {
      const wide = new BigIntDomain(0n, 1000n);
      const narrow = new BigIntDomain(100n, 500n);
      expect(narrow.encapsulates(wide).result).toBe('false');
    });

    it('equal ranges encapsulate each other', () => {
      const a = new BigIntDomain(0n, 100n);
      const b = new BigIntDomain(0n, 100n);
      expect(a.encapsulates(b).result).toBe('true');
      expect(b.encapsulates(a).result).toBe('true');
    });

    it('non-overlapping ranges do not encapsulate', () => {
      const a = new BigIntDomain(0n, 100n);
      const b = new BigIntDomain(200n, 300n);
      expect(a.encapsulates(b).result).toBe('false');
      expect(b.encapsulates(a).result).toBe('false');
    });

    it('works with negative ranges', () => {
      const wide = new BigIntDomain(-1000n, 1000n);
      const narrow = new BigIntDomain(-500n, 500n);
      expect(wide.encapsulates(narrow).result).toBe('true');
    });

    it('works with very large bigints', () => {
      const huge = 10n ** 50n;
      const wide = new BigIntDomain(0n, huge);
      const narrow = new BigIntDomain(huge / 4n, huge / 2n);
      expect(wide.encapsulates(narrow).result).toBe('true');
    });

    describe('boundary conditions', () => {
      it('min boundary exactly at limit', () => {
        const outer = new BigIntDomain(0n, 100n);
        const inner = new BigIntDomain(0n, 50n);
        expect(outer.encapsulates(inner).result).toBe('true');
      });

      it('max boundary exactly at limit', () => {
        const outer = new BigIntDomain(0n, 100n);
        const inner = new BigIntDomain(50n, 100n);
        expect(outer.encapsulates(inner).result).toBe('true');
      });

      it('fails when inner min below outer min', () => {
        const outer = new BigIntDomain(10n, 100n);
        const inner = new BigIntDomain(5n, 50n);
        expect(outer.encapsulates(inner).result).toBe('false');
      });

      it('fails when inner max above outer max', () => {
        const outer = new BigIntDomain(0n, 100n);
        const inner = new BigIntDomain(50n, 150n);
        expect(outer.encapsulates(inner).result).toBe('false');
      });
    });

    it('returns type mismatch for non-BigIntDomain', () => {
      const bigint = new BigIntDomain(0n, 100n);
      const { ContiguousDomain } = require('@/com/techlloyd/janus/Domain');
      const contiguous = new ContiguousDomain('integer', 0, 100);
      expect(bigint.encapsulates(contiguous as any).result).toBe('false');
    });
  });
});

