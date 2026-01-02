import { ContiguousDomain } from "@/domains/ContiguousDomain";
import { AlternationDomain } from "@/domains/AlternationDomain";
import { Domains } from "@/index";

describe("ContiguousDomain", () => {
  it("bounds inclusively", () => {
    const domain = new ContiguousDomain(0, 5);
    expect(domain.contains(-1)).toBe(false);
    expect(domain.contains(0)).toBe(true);
    expect(domain.contains(5)).toBe(true);
    expect(domain.contains(6)).toBe(false);
  });

  it("rejects NaN", () => {
    const domain = new ContiguousDomain(0, 5);
    expect(domain.contains(Number.NaN)).toBe(false);
  });

  it("throws when min is greater than max", () => {
    expect(() => new ContiguousDomain(5, 0)).toThrow();
  });

  it("bigint domain rejects non-bigint values", () => {
    const domain = new ContiguousDomain<bigint>(0n, 5n);
    expect(domain.contains(1 as any)).toBe(false);
  });

  it("union merges overlapping ranges", () => {
    const left = new ContiguousDomain(0, 5);
    const right = new ContiguousDomain(3, 10);
    const unioned = Domains.set.union(left, right);
    expect(unioned).toBeInstanceOf(ContiguousDomain);
    const d = unioned as ContiguousDomain<number>;
    expect(d.min).toBe(0);
    expect(d.max).toBe(10);
  });

  it("intersect computes overlapping portion", () => {
    const left = new ContiguousDomain(0, 5);
    const right = new ContiguousDomain(3, 10);
    const intersected = Domains.set.intersect(left, right);
    expect(intersected).toBeInstanceOf(ContiguousDomain);
    const d = intersected as ContiguousDomain<number>;
    expect(d.min).toBe(3);
    expect(d.max).toBe(5);
  });

  it("subtract splits into alternation when punching holes", () => {
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
});

