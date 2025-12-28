import { ContiguousDomain } from "@/domain/contiguous/ContiguousDomain";
import { integerWitness } from "../helpers";

describe("AbstractDomain via ContiguousDomain", () => {
  const universe = ContiguousDomain.universe(0, 10, integerWitness);

  test("isDefinedAt and isEmpty", () => {
    const range = ContiguousDomain.range(universe, 2, 5);
    expect(range.isEmpty()).toBe(false);
    expect(range.isDefinedAt(2)).toBe(true);
    expect(range.isDefinedAt(6)).toBe(false);
  });

  test("union/intersect/complement behaviors", () => {
    const a = ContiguousDomain.range(universe, 0, 4);
    const b = ContiguousDomain.range(universe, 3, 8);
    const union = a.union(b) as ContiguousDomain<number>;
    expect(union.isDefinedAt(7)).toBe(true);
    const inter = a.intersect(b) as ContiguousDomain<number>;
    expect(inter.isDefinedAt(2)).toBe(false);
    expect(inter.isDefinedAt(3)).toBe(true);
    const comp = a.complement() as ContiguousDomain<number>;
    expect(comp.isDefinedAt(0)).toBe(false);
    expect(comp.isDefinedAt(9)).toBe(true);
  });

  test("encapsulates and equals", () => {
    const a = ContiguousDomain.range(universe, 0, 5);
    const b = ContiguousDomain.range(universe, 1, 4);
    const same = ContiguousDomain.range(universe, 0, 5);
    expect(a.encapsulates(b)).toBe(true);
    expect(a.equals(same)).toBe(true);
    expect(b.encapsulates(a)).toBe(false);
  });

  test("assertSameUniverse throws on mismatch", () => {
    const otherUniverse = ContiguousDomain.universe(100, 200, integerWitness);
    const a = ContiguousDomain.range(universe, 0, 5);
    const b = ContiguousDomain.range(otherUniverse, 101, 150);
    expect(() => a.union(b as any)).toThrow("Universe mismatch");
  });

  test("empty factory builds empty cert", () => {
    const empty = ContiguousDomain.empty(universe);
    expect(empty.isEmpty()).toBe(true);
  });
});

