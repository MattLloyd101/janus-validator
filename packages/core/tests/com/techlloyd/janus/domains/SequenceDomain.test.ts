import { SequenceDomain, FiniteDomain, ContiguousDomain, ContiguousType } from '@/com/techlloyd/janus/Domain';
import { DomainType } from '@/com/techlloyd/janus/domains/types';
import type { DomainsForTuple } from '@/com/techlloyd/janus/Types';

describe('SequenceDomain', () => {
  describe('construction', () => {
    it('creates domain with multiple parts', () => {
      const parts: DomainsForTuple<[number, string]> = [
        new FiniteDomain([1, 2]),
        new FiniteDomain(['a', 'b']),
      ];
      const seq = new SequenceDomain(parts);
      expect(seq.type).toBe(DomainType.SEQUENCE_DOMAIN);
      expect(seq.parts).toHaveLength(2);
    });

    it('creates single-element sequence', () => {
      const parts: DomainsForTuple<[number]> = [new FiniteDomain([1])];
      const seq = new SequenceDomain(parts);
      expect(seq.parts).toHaveLength(1);
    });

    it('creates empty sequence', () => {
      const seq = new SequenceDomain([]);
      expect(seq.parts).toHaveLength(0);
    });
  });

  describe('encapsulates', () => {
    it('encapsulates when all parts encapsulate', () => {
      const wider = new SequenceDomain([
        new ContiguousDomain(ContiguousType.INTEGER, 0, 100),
        new ContiguousDomain(ContiguousType.INTEGER, 0, 100),
      ]);
      const narrower = new SequenceDomain([
        new ContiguousDomain(ContiguousType.INTEGER, 10, 50),
        new ContiguousDomain(ContiguousType.INTEGER, 20, 60),
      ]);

      expect(wider.encapsulates(narrower).result).toBe('true');
    });

    it('does not encapsulate when any part fails', () => {
      const seq1 = new SequenceDomain([
        new ContiguousDomain(ContiguousType.INTEGER, 0, 100),
        new ContiguousDomain(ContiguousType.INTEGER, 0, 50), // narrower
      ]);
      const seq2 = new SequenceDomain([
        new ContiguousDomain(ContiguousType.INTEGER, 10, 50),
        new ContiguousDomain(ContiguousType.INTEGER, 0, 100), // exceeds
      ]);

      expect(seq1.encapsulates(seq2).result).toBe('false');
    });

    it('requires same number of parts', () => {
      const seq2 = new SequenceDomain([
        new FiniteDomain([1]),
        new FiniteDomain([2]),
      ]);
      const seq3 = new SequenceDomain([
        new FiniteDomain([1]),
        new FiniteDomain([2]),
        new FiniteDomain([3]),
      ]);

      expect(seq2.encapsulates(seq3 as any).result).toBe('false');
      expect(seq3.encapsulates(seq2 as any).result).toBe('false');
    });

    it('empty sequences encapsulate each other', () => {
      const empty1 = new SequenceDomain([]);
      const empty2 = new SequenceDomain([]);

      expect(empty1.encapsulates(empty2).result).toBe('true');
    });

    it('non-empty does not encapsulate empty (different lengths)', () => {
      const nonEmpty = new SequenceDomain([new FiniteDomain([1])]);
      const empty = new SequenceDomain([]);

      expect(nonEmpty.encapsulates(empty as any).result).toBe('false');
    });

    it('handles heterogeneous part types', () => {
      const seq1 = new SequenceDomain([
        new FiniteDomain([1, 2, 3]),
        new ContiguousDomain(ContiguousType.INTEGER, 0, 100),
      ]);
      const seq2 = new SequenceDomain([
        new FiniteDomain([2]),
        new ContiguousDomain(ContiguousType.INTEGER, 50, 75),
      ]);

      expect(seq1.encapsulates(seq2).result).toBe('true');
    });
  });
});
