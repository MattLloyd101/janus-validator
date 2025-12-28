import { ContinuousDomain, FiniteDomain, UnionDomain } from '@/com/techlloyd/janus';

describe('ContinuousDomain', () => {
  it('rejects non-finite bounds', () => {
    expect(() => ContinuousDomain.of(Number.NaN, 1)).toThrow(/finite min\/max/);
    expect(() => ContinuousDomain.of(0, Number.POSITIVE_INFINITY)).toThrow(/finite min\/max/);
  });

  it('empty domain when min > max', () => {
    const d = ContinuousDomain.of(2, 1);
    expect(d.isEmpty()).toBe(true);
    expect(d.isDefinedAt(1.5)).toBe(false);
  });

  it('isDefinedAt checks finite membership in [min,max]', () => {
    const d = ContinuousDomain.of(0, 1);
    expect(d.isDefinedAt(0)).toBe(true);
    expect(d.isDefinedAt(0.5)).toBe(true);
    expect(d.isDefinedAt(1)).toBe(true);
    expect(d.isDefinedAt(-0.01)).toBe(false);
    expect(d.isDefinedAt(Number.NaN)).toBe(false);
    expect(d.isDefinedAt(Number.POSITIVE_INFINITY)).toBe(false);
  });

  it('union merges overlapping/touching intervals', () => {
    const a = ContinuousDomain.of(0, 1);
    const b = ContinuousDomain.of(1, 2);
    const u = a.union(b) as ContinuousDomain;
    expect(u).toBeInstanceOf(ContinuousDomain);
    expect(u.min).toBe(0);
    expect(u.max).toBe(2);
  });

  it('union of disjoint intervals returns UnionDomain', () => {
    const a = ContinuousDomain.of(0, 1);
    const b = ContinuousDomain.of(2, 3);
    const u = a.union(b);
    expect(u).toBeInstanceOf(UnionDomain);
  });

  it('union with a non-continuous Domain returns UnionDomain', () => {
    const a = ContinuousDomain.of(0, 1);
    const b = FiniteDomain.of([1, 2]);
    const u = a.union(b);
    expect(u).toBeInstanceOf(UnionDomain);
  });

  it('intersection returns the overlapped interval (or empty)', () => {
    const a = ContinuousDomain.of(0, 5);
    const b = ContinuousDomain.of(2, 3);
    const i = a.intersection(b) as ContinuousDomain;
    expect(i).toBeInstanceOf(ContinuousDomain);
    expect(i.min).toBe(2);
    expect(i.max).toBe(3);
  });

  it('intersection with UnionDomain delegates to distribution', () => {
    const a = UnionDomain.of(ContinuousDomain.of(0, 1), ContinuousDomain.of(2, 3));
    const b = ContinuousDomain.of(0.5, 2.5);
    const res = a.intersection(b);
    expect(res).toBeInstanceOf(UnionDomain);
  });

  it('intersection delegates when other is a UnionDomain', () => {
    const a = ContinuousDomain.of(0, 10);
    const u = UnionDomain.of(ContinuousDomain.of(0, 1), ContinuousDomain.of(20, 30));
    const res = a.intersection(u);
    // Only one part intersects, so the normalized result can be a single ContinuousDomain.
    expect(res.isDefinedAt(0.5)).toBe(true);
    expect(res.isDefinedAt(25)).toBe(false);
  });

  it('intersection of disjoint intervals returns an empty domain', () => {
    const a = ContinuousDomain.of(0, 1);
    const b = ContinuousDomain.of(2, 3);
    const i = a.intersection(b) as ContinuousDomain;
    expect(i.isEmpty()).toBe(true);
  });

  it('intersection with an empty interval returns empty', () => {
    const a = ContinuousDomain.of(0, 1);
    const b = ContinuousDomain.of(2, 1); // empty
    const i = a.intersection(b) as ContinuousDomain;
    expect(i.isEmpty()).toBe(true);
  });

  it('intersection throws for unknown Domain types (for now)', () => {
    const a = ContinuousDomain.of(0, 1);
    const b = FiniteDomain.of([0, 1]);
    expect(() => a.intersection(b as any)).toThrow(/Not implemented/);
  });

  it('difference can return a UnionDomain when subtracting a middle segment', () => {
    const a = ContinuousDomain.of(0, 10);
    const b = ContinuousDomain.of(3, 7);
    const d = a.difference(b);
    expect(d).toBeInstanceOf(UnionDomain);
  });

  it('difference can return only the left segment', () => {
    const a = ContinuousDomain.of(0, 10);
    const b = ContinuousDomain.of(5, 20);
    const d = a.difference(b) as ContinuousDomain;
    expect(d).toBeInstanceOf(ContinuousDomain);
    expect(d.min).toBe(0);
    expect(d.max).toBe(5);
  });

  it('difference can return only the right segment', () => {
    const a = ContinuousDomain.of(0, 10);
    const b = ContinuousDomain.of(-1, 5);
    const d = a.difference(b) as ContinuousDomain;
    expect(d).toBeInstanceOf(ContinuousDomain);
    expect(d.min).toBe(5);
    expect(d.max).toBe(10);
  });

  it('difference returns self when no overlap', () => {
    const a = ContinuousDomain.of(0, 1);
    const b = ContinuousDomain.of(2, 3);
    const d = a.difference(b) as ContinuousDomain;
    expect(d).toBeInstanceOf(ContinuousDomain);
    expect(d.min).toBe(0);
    expect(d.max).toBe(1);
  });

  it('difference returns empty when fully covered', () => {
    const a = ContinuousDomain.of(0, 1);
    const b = ContinuousDomain.of(-10, 10);
    const d = a.difference(b) as ContinuousDomain;
    expect(d.isEmpty()).toBe(true);
  });

  it('difference of empty domain is empty', () => {
    const a = ContinuousDomain.of(2, 1);
    const b = ContinuousDomain.of(0, 1);
    expect((a.difference(b) as ContinuousDomain).isEmpty()).toBe(true);
  });

  it('union with an empty interval returns the other interval (both directions)', () => {
    const empty = ContinuousDomain.of(2, 1);
    const a = ContinuousDomain.of(0, 1);
    expect((empty.union(a) as ContinuousDomain).equals(a)).toBe(true);
    expect((a.union(empty) as ContinuousDomain).equals(a)).toBe(true);
  });

  it('difference by an empty interval returns self', () => {
    const a = ContinuousDomain.of(0, 1);
    const empty = ContinuousDomain.of(2, 1);
    const d = a.difference(empty) as ContinuousDomain;
    expect(d.equals(a)).toBe(true);
  });

  it('difference throws for unknown Domain types (for now)', () => {
    const a = ContinuousDomain.of(0, 1);
    const b = FiniteDomain.of([0, 1]);
    expect(() => a.difference(b as any)).toThrow(/Not implemented/);
  });

  it('difference by a union subtracts sequentially', () => {
    const a = ContinuousDomain.of(0, 10);
    const sub = UnionDomain.of(ContinuousDomain.of(1, 2), ContinuousDomain.of(3, 4));
    const res = a.difference(sub);
    expect(res).toBeDefined();
  });
});


