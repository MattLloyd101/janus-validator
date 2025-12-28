import { ContiguousDomain, FiniteDomain, PiecewiseContiguousDomain, UnionDomain } from '@/com/techlloyd/janus';

describe('PiecewiseContiguousDomain', () => {
  const intOps = ContiguousDomain.of(0, 0).getIndexOps();
  const bigIntOps = ContiguousDomain.bigints(0n, 0n).getIndexOps();
  const charOps = ContiguousDomain.chars('a', 'a').getIndexOps();

  it('throws if fromContiguousDomains is called with no args', () => {
    expect(() => (PiecewiseContiguousDomain as any).fromContiguousDomains()).toThrow(/at least one domain/);
  });

  it('normalizes overlapping and adjacent ranges', () => {
    const d = PiecewiseContiguousDomain.fromContiguousDomains(
      ContiguousDomain.of(0, 2),
      ContiguousDomain.of(3, 5), // adjacent
      ContiguousDomain.of(4, 10) // overlap
    );
    expect(d.ranges).toEqual([{ minIndex: 0, maxIndex: 10 }]);
  });

  it('normalizes by rounding indices and filtering invalid ranges', () => {
    const d = PiecewiseContiguousDomain.fromIndexRanges(intOps, [
      { minIndex: 1.2, maxIndex: 1.8 }, // rounds to [2,1] -> filtered out
      { minIndex: 1.2, maxIndex: 2.8 }, // rounds to [2,2]
      { minIndex: Number.NaN, maxIndex: 5 }, // filtered
      { minIndex: 10, maxIndex: 12 },
    ]);
    expect(d.ranges).toEqual([
      { minIndex: 2, maxIndex: 2 },
      { minIndex: 10, maxIndex: 12 },
    ]);
  });

  it('fromNumberIndexRanges uses built-in number index ops', () => {
    const d = PiecewiseContiguousDomain.fromNumberIndexRanges([{ minIndex: 0, maxIndex: 2 }]);
    expect(d.isDefinedAt(1)).toBe(true);
    expect(d.isDefinedAt(1.5 as any)).toBe(false);
  });

  it('fromCharIndexRanges uses built-in char index ops', () => {
    const a = 'a'.codePointAt(0)!;
    const c = 'c'.codePointAt(0)!;
    const d = PiecewiseContiguousDomain.fromCharIndexRanges([{ minIndex: a, maxIndex: c }]);
    expect(d.isDefinedAt('a')).toBe(true);
    expect(d.isDefinedAt('b')).toBe(true);
    expect(d.isDefinedAt('d')).toBe(false);
  });

  it('fromBigIntIndexRanges uses built-in bigint index ops', () => {
    const d = PiecewiseContiguousDomain.fromBigIntIndexRanges([{ minIndex: 0n, maxIndex: 2n }]);
    expect(d.isDefinedAt(1n)).toBe(true);
    expect(d.isDefinedAt(3n)).toBe(false);
  });

  it('ContiguousDomain.piecewiseBigints builds a normalized piecewise domain from bigint ranges', () => {
    const d = ContiguousDomain.piecewiseBigints([0n, 2n], [3n, 5n], [10n, 12n]);
    // first two ranges are adjacent -> merged; 10-12 stays separate
    expect(d.isDefinedAt(0n)).toBe(true);
    expect(d.isDefinedAt(5n)).toBe(true);
    expect(d.isDefinedAt(9n)).toBe(false);
    expect(d.isDefinedAt(11n)).toBe(true);
  });

  it('fromIndexRanges requires IndexMath for custom ops', () => {
    const customOps = {
      toIndex: (v: number) => v,
      fromIndex: (i: number) => i,
    };
    expect(() => PiecewiseContiguousDomain.fromIndexRanges(customOps, [{ minIndex: 0, maxIndex: 1 }])).toThrow(
      /requires an IndexMath/
    );
  });

  it('fromIndexRanges can infer IndexMath for built-in char ops', () => {
    const a = 'a'.codePointAt(0)!;
    const d = PiecewiseContiguousDomain.fromIndexRanges(charOps, [{ minIndex: a, maxIndex: a }]);
    expect(d.isDefinedAt('a')).toBe(true);
    expect(d.isDefinedAt('b')).toBe(false);
  });

  it('sorts by maxIndex when minIndex ties', () => {
    const d = PiecewiseContiguousDomain.fromIndexRanges(intOps, [
      { minIndex: 0, maxIndex: 0 },
      { minIndex: 10, maxIndex: 10 },
      { minIndex: 0, maxIndex: 5 },
    ]);
    expect(d.ranges).toEqual([
      { minIndex: 0, maxIndex: 5 },
      { minIndex: 10, maxIndex: 10 },
    ]);
  });

  it('normalizes undefined/empty range input to empty', () => {
    const d0 = PiecewiseContiguousDomain.fromIndexRanges(intOps, undefined as any);
    expect(d0.isEmpty()).toBe(true);

    const d1 = PiecewiseContiguousDomain.fromIndexRanges(intOps, [
      { minIndex: 5, maxIndex: 4 }, // invalid
    ]);
    expect(d1.isEmpty()).toBe(true);
  });

  it('membership uses binary search over ranges', () => {
    const d = PiecewiseContiguousDomain.fromContiguousDomains(ContiguousDomain.of(0, 1), ContiguousDomain.of(10, 12));
    expect(d.isDefinedAt(0)).toBe(true);
    expect(d.isDefinedAt(2)).toBe(false);
    expect(d.isDefinedAt(11)).toBe(true);
  });

  it('isDefinedAt is false for non-integer numbers (discrete domain)', () => {
    const d = PiecewiseContiguousDomain.fromContiguousDomains(ContiguousDomain.of(0, 10));
    expect(d.isDefinedAt(1.5 as any)).toBe(false);
  });

  it('isDefinedAt is false for empty piecewise domains', () => {
    const d = PiecewiseContiguousDomain.fromIndexRanges(intOps, []);
    expect(d.isDefinedAt(0)).toBe(false);
  });

  it('union with a compatible ContiguousDomain returns a normalized piecewise domain', () => {
    const p = PiecewiseContiguousDomain.fromContiguousDomains(ContiguousDomain.of(0, 2), ContiguousDomain.of(10, 12));
    const res = p.union(ContiguousDomain.of(3, 9)) as PiecewiseContiguousDomain<number>;
    expect(res).toBeInstanceOf(PiecewiseContiguousDomain);
    // merges to [0,12]
    expect(res.ranges).toEqual([{ minIndex: 0, maxIndex: 12 }]);
  });

  it('union with a UnionDomain delegates to the UnionDomain', () => {
    const p = PiecewiseContiguousDomain.fromContiguousDomains(ContiguousDomain.of(0, 1));
    const u = UnionDomain.of<number>(FiniteDomain.of([99]));
    const res = p.union(u);
    expect(res).toBeInstanceOf(UnionDomain);
  });

  it('union with another piecewise (same ops) merges ranges', () => {
    const a = PiecewiseContiguousDomain.fromContiguousDomains(ContiguousDomain.of(0, 1));
    const b = PiecewiseContiguousDomain.fromContiguousDomains(ContiguousDomain.of(2, 3));
    const u = a.union(b) as PiecewiseContiguousDomain<number>;
    expect(u).toBeInstanceOf(PiecewiseContiguousDomain);
    expect(u.ranges).toEqual([{ minIndex: 0, maxIndex: 3 }]);
  });

  it('union with an unrelated Domain returns UnionDomain', () => {
    const a = PiecewiseContiguousDomain.fromContiguousDomains(ContiguousDomain.of(0, 1));
    const f = FiniteDomain.of([0, 1]);
    const u = a.union(f);
    expect(u).toBeInstanceOf(UnionDomain);
  });

  it('union with an incompatible ContiguousDomain returns UnionDomain', () => {
    const a = PiecewiseContiguousDomain.fromContiguousDomains(ContiguousDomain.of(0, 1));
    const c = ContiguousDomain.chars('a', 'b') as any;
    const u = a.union(c);
    expect(u).toBeInstanceOf(UnionDomain);
  });

  it('intersection works with both ContiguousDomain and PiecewiseContiguousDomain', () => {
    const a = PiecewiseContiguousDomain.fromIndexRanges(intOps, [
      { minIndex: 0, maxIndex: 5 },
      { minIndex: 10, maxIndex: 12 },
    ]);
    const i1 = a.intersection(ContiguousDomain.of(3, 11)) as PiecewiseContiguousDomain<number>;
    expect(i1.ranges).toEqual([
      { minIndex: 3, maxIndex: 5 },
      { minIndex: 10, maxIndex: 11 },
    ]);

    const b = PiecewiseContiguousDomain.fromContiguousDomains(ContiguousDomain.of(4, 4), ContiguousDomain.of(11, 20));
    const i2 = a.intersection(b) as PiecewiseContiguousDomain<number>;
    expect(i2.ranges).toEqual([
      { minIndex: 4, maxIndex: 4 },
      { minIndex: 11, maxIndex: 12 },
    ]);
  });

  it('difference works with both ContiguousDomain and PiecewiseContiguousDomain', () => {
    const a = PiecewiseContiguousDomain.fromContiguousDomains(ContiguousDomain.of(0, 10));
    const d1 = a.difference(ContiguousDomain.of(3, 7)) as PiecewiseContiguousDomain<number>;
    expect(d1.ranges).toEqual([
      { minIndex: 0, maxIndex: 2 },
      { minIndex: 8, maxIndex: 10 },
    ]);

    const sub = PiecewiseContiguousDomain.fromIndexRanges(intOps, [
      { minIndex: 2, maxIndex: 3 },
      { minIndex: 7, maxIndex: 8 },
    ]);
    const d2 = a.difference(sub) as PiecewiseContiguousDomain<number>;
    expect(d2.ranges).toEqual([
      { minIndex: 0, maxIndex: 1 },
      { minIndex: 4, maxIndex: 6 },
      { minIndex: 9, maxIndex: 10 },
    ]);
  });

  it('difference skips subtractor ranges that are entirely before the current segment', () => {
    const a = PiecewiseContiguousDomain.fromIndexRanges(intOps, [
      { minIndex: 10, maxIndex: 12 },
      { minIndex: 20, maxIndex: 22 },
    ]);
    const b = PiecewiseContiguousDomain.fromIndexRanges(intOps, [
      { minIndex: 0, maxIndex: 5 }, // entirely before first segment
      { minIndex: 11, maxIndex: 11 },
    ]);
    const d = a.difference(b) as PiecewiseContiguousDomain<number>;
    expect(d.ranges).toEqual([
      { minIndex: 10, maxIndex: 10 },
      { minIndex: 12, maxIndex: 12 },
      { minIndex: 20, maxIndex: 22 },
    ]);
  });

  it('difference by a UnionDomain subtracts sequentially', () => {
    const a = PiecewiseContiguousDomain.fromContiguousDomains(ContiguousDomain.of(0, 10));
    const sub = UnionDomain.of<number>(ContiguousDomain.of(2, 2), ContiguousDomain.of(4, 4));
    const res = a.difference(sub) as PiecewiseContiguousDomain<number>;
    expect(res.isDefinedAt(2)).toBe(false);
    expect(res.isDefinedAt(4)).toBe(false);
    expect(res.isDefinedAt(3)).toBe(true);
  });

  it('bigint domains handle values beyond Number.MAX_SAFE_INTEGER', () => {
    const maxSafe = BigInt(Number.MAX_SAFE_INTEGER);
    const a = ContiguousDomain.bigints(maxSafe - 2n, maxSafe + 2n);
    const b = ContiguousDomain.bigints(maxSafe, maxSafe);
    const d = a.difference(b);
    expect(d.isDefinedAt(maxSafe)).toBe(false);
    expect(d.isDefinedAt(maxSafe - 1n)).toBe(true);
    expect(d.isDefinedAt(maxSafe + 1n)).toBe(true);
  });

  it('bigint piecewise operations work (union/intersection/difference)', () => {
    const p = PiecewiseContiguousDomain.fromIndexRanges(bigIntOps, [
      { minIndex: 0n, maxIndex: 2n },
      { minIndex: 10n, maxIndex: 12n },
    ]);
    const u = p.union(ContiguousDomain.bigints(3n, 9n)) as PiecewiseContiguousDomain<bigint, bigint>;
    expect(u.isDefinedAt(11n)).toBe(true);

    const i = p.intersection(ContiguousDomain.bigints(2n, 10n)) as PiecewiseContiguousDomain<bigint, bigint>;
    expect(i.isDefinedAt(1n)).toBe(false);
    expect(i.isDefinedAt(2n)).toBe(true);
    expect(i.isDefinedAt(10n)).toBe(true);

    const d = p.difference(ContiguousDomain.bigints(1n, 11n)) as PiecewiseContiguousDomain<bigint, bigint>;
    expect(d.isDefinedAt(0n)).toBe(true);
    expect(d.isDefinedAt(1n)).toBe(false);
    expect(d.isDefinedAt(12n)).toBe(true);
  });

  it('difference breaks early when subtraction fully covers a segment', () => {
    const a = PiecewiseContiguousDomain.fromContiguousDomains(ContiguousDomain.of(0, 10));
    const b = PiecewiseContiguousDomain.fromContiguousDomains(ContiguousDomain.of(0, 10));
    const d = a.difference(b);
    expect(d.isEmpty()).toBe(true);
  });

  it('fromContiguousDomains rejects incompatible ops', () => {
    expect(() =>
      PiecewiseContiguousDomain.fromContiguousDomains(
        ContiguousDomain.of(0, 1) as any,
        ContiguousDomain.chars('a', 'b') as any
      )
    ).toThrow(/compatible ContiguousDomain ops/);
  });

  it('intersection/difference throw for incompatible ops', () => {
    const a = PiecewiseContiguousDomain.fromContiguousDomains(ContiguousDomain.of(0, 1));
    const b = ContiguousDomain.chars('a', 'b') as any;
    expect(() => a.intersection(b)).toThrow(/Not implemented/);
    expect(() => a.difference(b)).toThrow(/Not implemented/);
  });

  it('intersection/difference throw for unsupported domain types', () => {
    const a = PiecewiseContiguousDomain.fromContiguousDomains(ContiguousDomain.of(0, 1));
    const f = FiniteDomain.of([0, 1]) as any;
    expect(() => a.intersection(f)).toThrow(/Not implemented/);
    expect(() => a.difference(f)).toThrow(/Not implemented/);
  });

  it('intersection with a UnionDomain delegates to distribution', () => {
    const a = PiecewiseContiguousDomain.fromContiguousDomains(ContiguousDomain.of(0, 10));
    const u = UnionDomain.of<number>(ContiguousDomain.of(0, 1), ContiguousDomain.of(20, 30));
    const res = a.intersection(u);
    expect(res).toBeDefined();
  });

  it('ContiguousDomain.difference that splits returns PiecewiseContiguousDomain', () => {
    const a = ContiguousDomain.of(0, 9);
    const b = ContiguousDomain.of(2, 6);
    const d = a.difference(b);
    expect(d).toBeInstanceOf(PiecewiseContiguousDomain);
  });
});


