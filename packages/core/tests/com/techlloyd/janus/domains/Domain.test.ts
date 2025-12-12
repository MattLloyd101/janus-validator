/**
 * Tests for base Domain class behavior and common encapsulation logic.
 */

import {
  Domain,
  FiniteDomain,
  ContiguousDomain,
  ContiguousType,
  AlternationDomain,
  CustomGeneratorDomain,
  CaptureDomain,
  RefDomain,
} from '@/com/techlloyd/janus/Domain';

describe('Domain base class', () => {
  describe('encapsulates - CustomGeneratorDomain unwrapping', () => {
    it('unwraps CustomGeneratorDomain from other before comparison', () => {
      const inner = new FiniteDomain([1, 2, 3]);
      const wrapped = new CustomGeneratorDomain(inner, () => 1);
      const wider = new FiniteDomain([0, 1, 2, 3, 4]);

      // wider should encapsulate the wrapped domain (by unwrapping first)
      expect(wider.encapsulates(wrapped).result).toBe('true');
    });

    it('handles nested CustomGeneratorDomain wrapping', () => {
      const inner = new FiniteDomain([1, 2]);
      const wrapped1 = new CustomGeneratorDomain(inner, () => 1);
      const wrapped2 = new CustomGeneratorDomain(wrapped1, () => 2);
      const wider = new FiniteDomain([0, 1, 2, 3]);

      expect(wider.encapsulates(wrapped2).result).toBe('true');
    });
  });

  describe('encapsulates - AlternationDomain handling', () => {
    it('encapsulates alternation if it encapsulates all alternatives', () => {
      const alt = new AlternationDomain([
        new FiniteDomain([1, 2]),
        new FiniteDomain([3, 4]),
      ]);
      const wider = new FiniteDomain([1, 2, 3, 4, 5]);

      expect(wider.encapsulates(alt).result).toBe('true');
    });

    it('does not encapsulate alternation if any alternative fails', () => {
      const alt = new AlternationDomain([
        new FiniteDomain([1, 2]),
        new FiniteDomain([100, 200]),
      ]);
      const partial = new FiniteDomain([1, 2, 3, 4]);

      expect(partial.encapsulates(alt).result).toBe('false');
    });

    it('handles CustomGeneratorDomain wrapped in AlternationDomain', () => {
      const inner1 = new FiniteDomain([1]);
      const inner2 = new FiniteDomain([2]);
      const wrapped = new CustomGeneratorDomain(inner2, () => 2);
      const alt = new AlternationDomain([inner1, wrapped]);
      const wider = new FiniteDomain([1, 2, 3]);

      expect(wider.encapsulates(alt).result).toBe('true');
    });
  });
});

describe('CustomGeneratorDomain', () => {
  describe('encapsulates', () => {
    it('delegates to inner domain for encapsulation check', () => {
      const inner = new FiniteDomain([1, 2, 3, 4, 5]);
      const custom = new CustomGeneratorDomain(inner, () => 1);
      const subset = new FiniteDomain([2, 3]);

      expect(custom.encapsulates(subset).result).toBe('true');
    });

    it('returns false when inner domain does not encapsulate', () => {
      const inner = new FiniteDomain([1, 2]);
      const custom = new CustomGeneratorDomain(inner, () => 1);
      const other = new FiniteDomain([3, 4]);

      expect(custom.encapsulates(other).result).toBe('false');
    });
  });
});

describe('CaptureDomain', () => {
  describe('encapsulates', () => {
    it('delegates to inner domain for encapsulation', () => {
      const inner = new ContiguousDomain(ContiguousType.INTEGER, 0, 10);
      const capture = new CaptureDomain('myCapture', inner);
      const subset = new ContiguousDomain(ContiguousType.INTEGER, 2, 8);

      expect(capture.encapsulates(subset).result).toBe('true');
    });

    it('compares capture name when both are CaptureDomain', () => {
      const inner = new ContiguousDomain(ContiguousType.INTEGER, 0, 10);
      const capture1 = new CaptureDomain('name1', inner);
      const capture2 = new CaptureDomain('name2', inner);

      // Different capture names - inner domains match but names differ
      // Should still work based on inner domain
      expect(capture1.encapsulates(capture2).result).toBe('true');
    });

    it('returns false when inner domain does not encapsulate', () => {
      const inner1 = new ContiguousDomain(ContiguousType.INTEGER, 0, 5);
      const inner2 = new ContiguousDomain(ContiguousType.INTEGER, 10, 20);
      const capture = new CaptureDomain('cap', inner1);

      expect(capture.encapsulates(inner2).result).toBe('false');
    });
  });
});

describe('RefDomain', () => {
  describe('encapsulates', () => {
    it('always returns unknown (cross-field constraint not supported)', () => {
      const ref1 = new RefDomain('ref1');
      const ref2 = new RefDomain('ref2');

      // RefDomain is a cross-field constraint and is not supported for encapsulation
      expect(ref1.encapsulates(ref2).result).toBe('unknown');
    });

    it('returns unknown even for same ref name', () => {
      const ref = new RefDomain('myRef');
      // RefDomain comparison is inherently undecidable without context
      expect(ref.encapsulates(ref).result).toBe('unknown');
    });
  });
});

describe('Domain type mismatches', () => {
  it('FiniteDomain does not encapsulate ContiguousDomain', () => {
    const finite = new FiniteDomain([1, 2, 3]);
    const contiguous = new ContiguousDomain(ContiguousType.INTEGER, 0, 10);

    expect(finite.encapsulates(contiguous as any).result).toBe('false');
  });

  it('ContiguousDomain does not encapsulate FiniteDomain', () => {
    const finite = new FiniteDomain([1, 2, 3]);
    const contiguous = new ContiguousDomain(ContiguousType.INTEGER, 0, 10);

    expect(contiguous.encapsulates(finite as any).result).toBe('false');
  });
});
