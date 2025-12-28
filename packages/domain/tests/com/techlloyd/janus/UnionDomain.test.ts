import { AbstractDomain, DomainType, FiniteDomain, UnionDomain } from '@/com/techlloyd/janus';

describe('UnionDomain', () => {
  it('flattens nested unions', () => {
    const a = FiniteDomain.of([1]);
    const b = FiniteDomain.of([2]);
    const c = FiniteDomain.of([3]);

    const u = UnionDomain.of(UnionDomain.of(a, b), c);
    expect(u.parts.length).toBe(3);
  });

  it('isDefinedAt is true if any part contains the value', () => {
    const a = FiniteDomain.of([1, 2]);
    const b = FiniteDomain.of([10]);
    const u = UnionDomain.of(a, b);
    expect(u.isDefinedAt(2)).toBe(true);
    expect(u.isDefinedAt(10)).toBe(true);
    expect(u.isDefinedAt(99)).toBe(false);
  });

  it('union returns a (flattened) UnionDomain', () => {
    const a = FiniteDomain.of([1]);
    const b = FiniteDomain.of([2]);
    const u = UnionDomain.of(a);
    const res = u.union(b);
    expect(res).toBeInstanceOf(UnionDomain);
    expect((res as UnionDomain<number>).parts.length).toBe(2);
  });

  it('isEmpty is false if any part is non-empty', () => {
    const u = UnionDomain.of(FiniteDomain.of([1]));
    expect(u.isEmpty()).toBe(false);
  });

  it('isEmpty is true if all parts are empty', () => {
    const u = UnionDomain.of(FiniteDomain.of([]));
    expect(u.isEmpty()).toBe(true);
  });

  it('intersection distributes over union', () => {
    const a = FiniteDomain.of([1, 2, 3]);
    const b = FiniteDomain.of([3, 4, 5]);
    const c = FiniteDomain.of([2, 3, 4]);

    const left = UnionDomain.of(a, b).intersection(c);
    const right = UnionDomain.of(a.intersection(c), b.intersection(c));

    expect(left.equals(right)).toBe(true);
  });

  it('intersection drops empty parts (can result in an empty union)', () => {
    const a = UnionDomain.of(FiniteDomain.of([1]));
    const res = a.intersection(FiniteDomain.of([2]));
    expect(res).toBeInstanceOf(UnionDomain);
    expect((res as UnionDomain<number>).isEmpty()).toBe(true);
  });

  it('difference drops empty parts (can result in an empty union)', () => {
    const a = UnionDomain.of(FiniteDomain.of([1]));
    const res = a.difference(FiniteDomain.of([1]));
    expect(res).toBeInstanceOf(UnionDomain);
    expect((res as UnionDomain<number>).isEmpty()).toBe(true);
  });

  it('difference distributes over union', () => {
    const a = FiniteDomain.of([1, 2, 3]);
    const b = FiniteDomain.of([3, 4, 5]);
    const c = FiniteDomain.of([2, 4]);

    const left = UnionDomain.of(a, b).difference(c);
    const right = UnionDomain.of(a.difference(c), b.difference(c));

    expect(left.equals(right)).toBe(true);
  });

  it('difference by a union applies sequentially (A \\ (B∪C) = (A\\B)\\C)', () => {
    const a = FiniteDomain.of([1, 2, 3, 4, 5]);
    const b = FiniteDomain.of([2, 3]);
    const c = FiniteDomain.of([4]);

    const u = UnionDomain.of(a);
    const left = u.difference(UnionDomain.of(b, c));
    const right = u.difference(b).difference(c);

    expect(left.equals(right)).toBe(true);
  });

  it('intersection with a union distributes to pairwise intersections', () => {
    const a = FiniteDomain.of([1, 2, 3]);
    const b = FiniteDomain.of([3, 4]);
    const c = FiniteDomain.of([2, 3]);
    const d = FiniteDomain.of([3]);

    const left = UnionDomain.of(a, b).intersection(UnionDomain.of(c, d));
    const right = UnionDomain.of(a.intersection(c), a.intersection(d), b.intersection(c), b.intersection(d));

    expect(left.equals(right)).toBe(true);
  });

  it('empty union behaves as the empty set under intersection/difference', () => {
    const empty = UnionDomain.of<number>();
    const a = FiniteDomain.of([1, 2, 3]);

    expect(empty.isEmpty()).toBe(true);
    expect(empty.intersection(a).isEmpty()).toBe(true);
    expect(empty.difference(a).isEmpty()).toBe(true);
    const res = UnionDomain.of(a).difference(empty);
    expect(res).toBeInstanceOf(UnionDomain);
    expect((res as UnionDomain<number>).parts).toEqual([a]);
  });

  it('A ∩ ∅ = ∅ when both sides are unions', () => {
    const a = UnionDomain.of(FiniteDomain.of([1, 2, 3]));
    const empty = UnionDomain.of<number>();
    expect(a.intersection(empty).isEmpty()).toBe(true);
  });

  it('intersection normalizes nested UnionDomain results', () => {
    class ReturnsUnionOnIntersection extends AbstractDomain<number> {
      readonly domainType = DomainType.FINITE_DOMAIN;
      readonly universe = this;
      isEmpty(): boolean { return false; }
      isDefinedAt(_value: number): boolean { return false; }
      union(other: any): any { return other; }
      intersection(_other: any): any { return UnionDomain.of(FiniteDomain.of([1])); }
      difference(_other: any): any { return this; }
    }

    const a = new ReturnsUnionOnIntersection();
    const b = new ReturnsUnionOnIntersection();
    const u = UnionDomain.of(a, b);
    const res = u.intersection(FiniteDomain.of([0]));
    expect(res).toBeInstanceOf(UnionDomain);
  });
});


