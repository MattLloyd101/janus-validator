import { AbstractDomain, Domain, DomainType, FiniteDomain, UnionDomain } from '@/com/techlloyd/janus';
import * as Domains from '@/com/techlloyd/janus/domains';

describe('FiniteDomain', () => {
  it('barrel exports work via com/techlloyd/janus/domains', () => {
    expect(Domains.DomainType.FINITE_DOMAIN).toBe('FINITE_DOMAIN');
    expect(Domains.FiniteDomain).toBeDefined();
    expect(typeof Domains.AbstractDomain).toBe('function');
  });

  it('has domainType FINITE_DOMAIN', () => {
    const d = FiniteDomain.of([1, 2, 3]);
    expect(d.domainType).toBe(DomainType.FINITE_DOMAIN);
  });

  it('defaults universe to itself (root domain)', () => {
    const d = FiniteDomain.of([1, 2, 3]);
    expect(d.universe).toBe(d);
  });

  it('isEmpty reflects whether there are any values', () => {
    expect(FiniteDomain.of([]).isEmpty()).toBe(true);
    expect(FiniteDomain.of([1]).isEmpty()).toBe(false);
  });

  it('isDefinedAt checks membership', () => {
    const d = FiniteDomain.of([1, 2, 3]);
    expect(d.isDefinedAt(2)).toBe(true);
    expect(d.isDefinedAt(99)).toBe(false);
  });

  it('isSubsetOf / isSupersetOf work via set difference', () => {
    const a = FiniteDomain.of([1, 2]);
    const b = FiniteDomain.of([1, 2, 3]);

    expect(a.isSubsetOf(b)).toBe(true);
    expect(b.isSupersetOf(a)).toBe(true);

    expect(b.isSubsetOf(a)).toBe(false);
    expect(a.isSupersetOf(b)).toBe(false);

    // Reflexive
    expect(a.isSubsetOf(a)).toBe(true);
    expect(a.isSupersetOf(a)).toBe(true);
    expect(a.equals(a)).toBe(true);
  });

  it('deduplicates values while preserving first-seen order', () => {
    const d = FiniteDomain.of([3, 1, 3, 2, 2, 1]);
    expect(d.values).toEqual([3, 1, 2]);
  });

  it('treats nullish values input as empty (defensive)', () => {
    // This intentionally bypasses TS typing to cover the defensive `values ?? []` branch.
    const d = FiniteDomain.of(undefined as unknown as readonly number[]);
    expect(d.values).toEqual([]);
    expect(d.universe).toBe(d);
  });

  it('reductive ops retain the parent universe reference', () => {
    const universe = FiniteDomain.of([1, 2, 3, 4, 5]);
    const a = universe.intersection(FiniteDomain.of([2, 3, 4]));

    expect(a).not.toBe(universe);
    expect(a.universe).toBe(universe);

    const b = a.difference(FiniteDomain.of([3]));
    expect(b.universe).toBe(universe);

    // complement is implemented by AbstractDomain as universe.difference(this)
    const c = b.complement() as FiniteDomain<number>;
    expect(c.universe).toBe(universe);
    expect(c.values).toEqual([1, 3, 5]);
  });

  it('intersection computes set intersection (left order preserved)', () => {
    const d = FiniteDomain.of([3, 1, 2]);
    const i = d.intersection(FiniteDomain.of([2, 3, 9]));
    expect(i.values).toEqual([3, 2]);
  });

  it('difference computes set difference (left order preserved)', () => {
    const d = FiniteDomain.of([3, 1, 2]);
    const x = d.difference(FiniteDomain.of([1, 9]));
    expect(x.values).toEqual([3, 2]);
  });

  it('union is expansive and sets universe to the new result', () => {
    const universe = FiniteDomain.of([1, 2, 3]);
    const a = universe.intersection(FiniteDomain.of([1, 2]));

    const u = a.union(FiniteDomain.of([3, 4]));
    expect(u).toBeInstanceOf(FiniteDomain);
    const uf = u as FiniteDomain<number>;
    expect(uf.universe).toBe(uf);
    expect(uf.domainType).toBe(DomainType.FINITE_DOMAIN);
    expect(uf.values).toEqual([1, 2, 3, 4]);
  });

  it('complement uses the root universe even after multiple reductions', () => {
    const universe = FiniteDomain.of([1, 2, 3, 4, 5, 6]);
    const reduced = universe
      .intersection(FiniteDomain.of([2, 3, 4, 5]))
      .difference(FiniteDomain.of([3, 5]));

    expect(reduced.universe).toBe(universe);
    const comp = reduced.complement() as FiniteDomain<number>;
    expect(comp.universe).toBe(universe);
    expect(comp.values).toEqual([1, 3, 5, 6]);
  });

  it('can intersect/difference with a non-finite Domain via isDefinedAt', () => {
    class OnlyEven extends AbstractDomain<number> implements Domain<number> {
      readonly domainType = DomainType.FINITE_DOMAIN;
      readonly universe = this;
      isEmpty(): boolean { return false; }
      isDefinedAt(v: number): boolean { return v % 2 === 0; }
      union(other: Domain<number>): Domain<number> { return UnionDomain.of(this, other); }
      intersection(_other: Domain<number>): Domain<number> { throw new Error('Not implemented'); }
      difference(_other: Domain<number>): Domain<number> { throw new Error('Not implemented'); }
    }

    const d = FiniteDomain.of([1, 2, 3, 4, 5]);
    const even = new OnlyEven();

    expect(d.intersection(even).values).toEqual([2, 4]);
    expect(d.difference(even).values).toEqual([1, 3, 5]);
  });

  it('union with a non-finite Domain returns UnionDomain', () => {
    class OnlyEven extends AbstractDomain<number> {
      readonly domainType = DomainType.FINITE_DOMAIN;
      readonly universe = this;
      isEmpty(): boolean { return false; }
      isDefinedAt(v: number): boolean { return v % 2 === 0; }
      union(other: Domain<number>): Domain<number> { return UnionDomain.of(this, other); }
      intersection(_other: Domain<number>): Domain<number> { throw new Error('Not implemented'); }
      difference(_other: Domain<number>): Domain<number> { throw new Error('Not implemented'); }
    }

    const d = FiniteDomain.of([1, 2, 3]);
    const even = new OnlyEven();
    const u = d.union(even);
    expect(u).toBeInstanceOf(UnionDomain);
  });
});


