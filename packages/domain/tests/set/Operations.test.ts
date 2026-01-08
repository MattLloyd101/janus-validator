import { ContiguousDomain } from "@/domains/ContiguousDomain";
import { AlternationDomain } from "@/domains/AlternationDomain";
import { FiniteDomain } from "@/domains/FiniteDomain";
import { StringDomain } from "@/domains/StringDomain";
import { BytesDomain } from "@/domains/BytesDomain";
import { Domains } from "@/index";

describe("Set operations", () => {
  it("union merges overlapping contiguous domains", () => {
    const left = new ContiguousDomain(0, 5);
    const right = new ContiguousDomain(3, 10);
    const unioned = Domains.set.union<unknown>(left, right);
    expect(unioned).toBeInstanceOf(ContiguousDomain);
    const d = unioned as ContiguousDomain<number>;
    expect(d.min).toBe(0);
    expect(d.max).toBe(10);
  });

  it("intersect produces overlapping portion", () => {
    const left = new ContiguousDomain(0, 5);
    const right = new ContiguousDomain(3, 10);
    const intersected = Domains.set.intersect(left, right);
    expect(intersected).toBeInstanceOf(ContiguousDomain);
    const d = intersected as ContiguousDomain<number>;
    expect(d.min).toBe(3);
    expect(d.max).toBe(5);
  });

  it("subtract splits into alternation when removing interior slice", () => {
    const universe = new ContiguousDomain(0, 10);
    const hole = new ContiguousDomain(3, 7);
    const result = Domains.set.subtract(universe, hole);
    expect(result).toBeInstanceOf(AlternationDomain);
    const parts = (result as AlternationDomain<number>).options;
    expect(parts).toHaveLength(2);
    expect((parts[0] as ContiguousDomain<number>).min).toBe(0);
    expect((parts[0] as ContiguousDomain<number>).max).toBe(2);
    expect((parts[1] as ContiguousDomain<number>).min).toBe(8);
    expect((parts[1] as ContiguousDomain<number>).max).toBe(10);
  });

  it("union merges finite sets", () => {
    const left = new FiniteDomain([1, 2]);
    const right = new FiniteDomain([2, 3]);
    const merged = Domains.set.union(left, right) as FiniteDomain<number>;
    expect(merged.contains(1)).toBe(true);
    expect(merged.contains(3)).toBe(true);
  });

  it("union of disjoint ranges yields alternation", () => {
    const left = new ContiguousDomain(0, 1);
    const right = new ContiguousDomain(5, 6);
    const unioned = Domains.set.union<unknown>(left, right);
    expect(unioned).toBeInstanceOf(AlternationDomain);
  });

  it("intersect disjoint ranges yields empty finite", () => {
    const left = new ContiguousDomain(0, 1);
    const right = new ContiguousDomain(5, 6);
    const intersected = Domains.set.intersect(left, right);
    expect(intersected).toBeInstanceOf(FiniteDomain);
    expect((intersected as FiniteDomain<number>).all.length).toBe(0);
  });

  it("intersect with alternation distributes", () => {
    const alt = new AlternationDomain<number>([new ContiguousDomain(0, 1), new ContiguousDomain(5, 6)]);
    const c = new ContiguousDomain(0, 5);
    const result = Domains.set.intersect(alt, c);
    expect(result.contains(0)).toBe(true);
    expect(result.contains(5)).toBe(true);
    expect(result.contains(6)).toBe(false);
  });

  it("subtract throws on unsupported combination", () => {
    const left = new StringDomain({ minLength: 1, maxLength: 3 });
    const right = new FiniteDomain(["a"]);
    expect(() => Domains.set.subtract(left, right)).toThrow("Unsupported subtract combination");
  });

  it("subtract finite removes values", () => {
    const left = new FiniteDomain([1, 2, 3]);
    const right = new FiniteDomain([2]);
    const result = Domains.set.subtract(left, right) as FiniteDomain<number>;
    expect(result.contains(2)).toBe(false);
    expect(result.contains(1)).toBe(true);
  });

  it("union fallback creates alternation for mixed kinds", () => {
    const left = new FiniteDomain([1]);
    const right = new StringDomain({ minLength: 1, maxLength: 1 });
    const unioned = Domains.set.union<unknown>(left, right);
    expect(unioned).toBeInstanceOf(AlternationDomain);
  });

  it("intersect finite domains returns intersection", () => {
    const left = new FiniteDomain([1, 2]);
    const right = new FiniteDomain([2, 3]);
    const result = Domains.set.intersect(left, right) as FiniteDomain<number>;
    expect(result.contains(2)).toBe(true);
    expect(result.all.length).toBe(1);
  });

  it("intersect handles alternation on right", () => {
    const alt = new AlternationDomain<number>([new ContiguousDomain(0, 0), new ContiguousDomain(10, 10)]);
    const left = new ContiguousDomain(0, 5);
    const result = Domains.set.intersect(left, alt);
    expect(result.contains(0)).toBe(true);
    expect(result.contains(10)).toBe(false);
  });

  it("subtract alternation maps over options", () => {
    const alt = new AlternationDomain<number>([new ContiguousDomain(0, 2), new ContiguousDomain(5, 6)]);
    const hole = new ContiguousDomain(1, 5);
    const result = Domains.set.subtract(alt, hole);
    expect(result.contains(0)).toBe(true);
    expect(result.contains(2)).toBe(false);
    expect(result.contains(6)).toBe(true);
  });

  it("intersect unsupported kinds yields empty finite", () => {
    const a = new StringDomain({ minLength: 1, maxLength: 2 });
    const b = new BytesDomain({ minLength: 1, maxLength: 2 });
    const result = Domains.set.intersect<unknown>(a, b);
    expect(result).toBeInstanceOf(FiniteDomain);
    expect((result as FiniteDomain<any>).all.length).toBe(0);
  });

  it("union with bigints respects adjacency branch", () => {
    const a = new ContiguousDomain<bigint>(0n, 1n);
    const b = new ContiguousDomain<bigint>(3n, 4n);
    const merged = Domains.set.union(a, b);
    expect(merged).toBeInstanceOf(AlternationDomain);
    const adjacentMerge = Domains.set.union(a, new ContiguousDomain<bigint>(2n, 4n));
    expect(adjacentMerge).toBeInstanceOf(ContiguousDomain);
  });

  it("union chooses min/max from either side", () => {
    const left = new ContiguousDomain(5, 10);
    const right = new ContiguousDomain(0, 6);
    const merged = Domains.set.union(left, right) as ContiguousDomain<number>;
    expect(merged.min).toBe(0);
    expect(merged.max).toBe(10);
  });

  it("subtract contiguous with after-only branch", () => {
    const left = new ContiguousDomain(0, 5);
    const right = new ContiguousDomain(0, 3);
    const result = Domains.set.subtract(left, right) as ContiguousDomain<number>;
    expect(result.contains(0)).toBe(false);
    expect(result.contains(4)).toBe(true);
  });

  it("subtract contiguous with before-only branch", () => {
    const left = new ContiguousDomain(0, 5);
    const right = new ContiguousDomain(4, 10);
    const result = Domains.set.subtract(left, right) as ContiguousDomain<number>;
    expect(result.contains(0)).toBe(true);
    expect(result.contains(5)).toBe(false);
  });

  it("subtract contiguous fully covered returns empty finite", () => {
    const left = new ContiguousDomain(0, 5);
    const right = new ContiguousDomain(0, 5);
    const result = Domains.set.subtract(left, right);
    expect(result).toBeInstanceOf(FiniteDomain);
    expect((result as FiniteDomain<number>).all.length).toBe(0);
  });

  it("subtract contiguous disjoint returns original", () => {
    const left = new ContiguousDomain(0, 5);
    const right = new ContiguousDomain(10, 20);
    const result = Domains.set.subtract(left, right) as ContiguousDomain<number>;
    expect(result.contains(0)).toBe(true);
    expect(result.contains(5)).toBe(true);
  });

  it("subtract contiguous bigints splits around hole", () => {
    const left = new ContiguousDomain<bigint>(0n, 10n);
    const hole = new ContiguousDomain<bigint>(3n, 7n);
    const result = Domains.set.subtract(left, hole) as AlternationDomain<bigint>;
    expect(result.options).toHaveLength(2);
    expect((result.options[0] as ContiguousDomain<bigint>).max).toBe(2n);
    expect((result.options[1] as ContiguousDomain<bigint>).min).toBe(8n);
  });

  it("adjacent ranges merge in union", () => {
    const left = new ContiguousDomain(0, 1);
    const right = new ContiguousDomain(2, 3);
    const merged = Domains.set.union(left, right) as ContiguousDomain<number>;
    expect(merged.min).toBe(0);
    expect(merged.max).toBe(3);
  });
});

