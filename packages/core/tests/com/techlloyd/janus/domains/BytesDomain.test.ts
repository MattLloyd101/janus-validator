import { BytesDomain } from '@/com/techlloyd/janus/Domain';
import { DomainType } from '@/com/techlloyd/janus/domains/types';

describe('BytesDomain', () => {
  describe('construction', () => {
    it('creates domain with length bounds', () => {
      const domain = new BytesDomain(10, 100);
      expect(domain.type).toBe(DomainType.BYTES_DOMAIN);
      expect(domain.minLength).toBe(10);
      expect(domain.maxLength).toBe(100);
    });

    it('allows zero minimum length', () => {
      const domain = new BytesDomain(0, 50);
      expect(domain.minLength).toBe(0);
    });

    it('allows exact length (min === max)', () => {
      const domain = new BytesDomain(16, 16);
      expect(domain.minLength).toBe(domain.maxLength);
    });

    it('allows large max length', () => {
      const domain = new BytesDomain(0, 1000000);
      expect(domain.maxLength).toBe(1000000);
    });
  });

  describe('encapsulates', () => {
    it('wider bounds encapsulate narrower bounds', () => {
      const wide = new BytesDomain(0, 100);
      const narrow = new BytesDomain(10, 50);
      expect(wide.encapsulates(narrow).result).toBe('true');
    });

    it('narrower bounds do not encapsulate wider', () => {
      const wide = new BytesDomain(0, 100);
      const narrow = new BytesDomain(10, 50);
      expect(narrow.encapsulates(wide).result).toBe('false');
    });

    it('equal bounds encapsulate each other', () => {
      const a = new BytesDomain(5, 50);
      const b = new BytesDomain(5, 50);
      expect(a.encapsulates(b).result).toBe('true');
      expect(b.encapsulates(a).result).toBe('true');
    });

    it('handles exact length constraints', () => {
      const exact16 = new BytesDomain(16, 16);
      const range = new BytesDomain(8, 32);
      expect(range.encapsulates(exact16).result).toBe('true');
      expect(exact16.encapsulates(range).result).toBe('false');
    });

    describe('boundary conditions', () => {
      it('min boundary must be <= other min', () => {
        const outer = new BytesDomain(10, 100);
        const inner = new BytesDomain(5, 50); // min below outer.min
        expect(outer.encapsulates(inner).result).toBe('false');
      });

      it('max boundary must be >= other max', () => {
        const outer = new BytesDomain(0, 50);
        const inner = new BytesDomain(0, 100); // max above outer.max
        expect(outer.encapsulates(inner).result).toBe('false');
      });

      it('zero-length domains', () => {
        const zero = new BytesDomain(0, 0);
        const nonZero = new BytesDomain(1, 10);
        expect(nonZero.encapsulates(zero).result).toBe('false');
        expect(zero.encapsulates(nonZero).result).toBe('false');
      });
    });

    it('returns type mismatch for non-BytesDomain', () => {
      const bytes = new BytesDomain(0, 100);
      const { FiniteDomain } = require('@/com/techlloyd/janus/Domain');
      const finite = new FiniteDomain([1, 2, 3]);
      expect(bytes.encapsulates(finite as any).result).toBe('false');
    });
  });
});

