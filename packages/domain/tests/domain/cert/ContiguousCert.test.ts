import { ContiguousCert, FiniteCert } from "@/index";
import { integerWitness } from "../../helpers";

describe("ContiguousCert", () => {
  const base = new ContiguousCert(0, 10, integerWitness);
  const otherWitness = {
    id: "other",
    compare: (a: number, b: number) => a - b,
    succ: (x: number) => x + 1,
    pred: (x: number) => x - 1
  };

  test("contains and bounds", () => {
    expect(base.contains(0)).toBe(true);
    expect(base.contains(10)).toBe(true);
    expect(base.contains(11)).toBe(false);
  });

  test("encapsulates range and finite subset", () => {
    const subRange = new ContiguousCert(3, 5, integerWitness);
    expect(base.encapsulates(subRange)).toBe(true);
  });

  test("mergeContiguous merges overlaps, not different witnesses", () => {
    const a = new ContiguousCert(0, 2, integerWitness);
    const b = new ContiguousCert(3, 5, integerWitness);
    const c = new ContiguousCert(100, 200, otherWitness);
    const merged = ContiguousCert.mergeContiguous([a, b, c]);
    expect(merged.some((m) => m instanceof ContiguousCert && (m as ContiguousCert<number>).max === 5)).toBe(true);
    expect(merged.some((m) => m instanceof ContiguousCert && (m as ContiguousCert<number>).min === 100)).toBe(true);
  });

  test("equals depends on witness identity", () => {
    const same = new ContiguousCert(0, 10, integerWitness);
    const diffWitness = new ContiguousCert(0, 10, otherWitness);
    expect(base.equals(same)).toBe(true);
    expect(base.equals(diffWitness)).toBe(false);
  });

  test("encapsulates finite subset", () => {
    const finite = new FiniteCert([0, 1, 10]);
    expect(base.encapsulates(finite)).toBe(true);
    const outside = new FiniteCert([11]);
    expect(base.encapsulates(outside)).toBe(false);
  });

  test("adjacent ranges merge via succ adjacency", () => {
    const a = new ContiguousCert(0, 2, integerWitness);
    const b = new ContiguousCert(3, 4, integerWitness); // adjacent because succ(2) === 3
    const merged = ContiguousCert.mergeContiguous([a, b]);
    expect(merged.length).toBe(1);
    const only = merged[0] as ContiguousCert<number>;
    expect(only.min).toBe(0);
    expect(only.max).toBe(4);
  });

  test("mergeContiguous returns others when no contiguous entries", () => {
    const finite = new FiniteCert([1]);
    const merged = ContiguousCert.mergeContiguous([finite]);
    expect(merged.length).toBe(1);
    expect(merged[0]).toBe(finite);
  });

  test("encapsulates returns false for unsupported cert types", () => {
    const unknown = { isEmpty: () => false, contains: () => true } as any;
    expect(base.encapsulates(unknown)).toBe(false);
  });

  test("serialize includes witness id", () => {
    const serialized = base.serialize();
    expect(serialized.kind).toBe("contiguous");
    expect(serialized.witness.id).toBe("integer");
  });

  test("mergeContiguous keeps disjoint same-witness ranges separate", () => {
    const a = new ContiguousCert(0, 2, integerWitness);
    const b = new ContiguousCert(4, 6, integerWitness); // non-adjacent
    const merged = ContiguousCert.mergeContiguous([a, b]);
    expect(merged.length).toBe(2);
  });

  test("encapsulates empty cert", () => {
    expect(base.encapsulates(new FiniteCert([]))).toBe(true);
  });

  test("mergeContiguous does not merge when succ is undefined", () => {
    const noSucc = {
      id: "nosucc",
      compare: (a: number, b: number) => a - b,
      succ: (_x: number) => undefined,
      pred: (_x: number) => undefined
    };
    const a = new ContiguousCert(0, 2, noSucc);
    const b = new ContiguousCert(3, 4, noSucc); // touching but succ undefined
    const merged = ContiguousCert.mergeContiguous([a, b]);
    expect(merged.length).toBe(2);
  });

  test("mergeContiguous merges when edges equal (cmp === 0)", () => {
    const a = new ContiguousCert(0, 2, integerWitness);
    const b = new ContiguousCert(2, 4, integerWitness);
    const merged = ContiguousCert.mergeContiguous([a, b]);
    expect(merged.length).toBe(1);
  });

  test("mergeContiguous merges overlapping ranges", () => {
    const a = new ContiguousCert(0, 3, integerWitness);
    const b = new ContiguousCert(2, 5, integerWitness);
    const merged = ContiguousCert.mergeContiguous([a, b]);
    expect(merged.length).toBe(1);
    const only = merged[0] as ContiguousCert<number>;
    expect(only.min).toBe(0);
    expect(only.max).toBe(5);
  });

  test("mergeRanges chooses min/max from either side", () => {
    const a = new ContiguousCert(5, 7, integerWitness);
    const b = new ContiguousCert(1, 10, integerWitness);
    const merged = ContiguousCert.mergeContiguous([a, b]);
    expect(merged.length).toBe(1);
    const only = merged[0] as ContiguousCert<number>;
    expect(only.min).toBe(1);
    expect(only.max).toBe(10);
  });

  test("mergeRanges chooses max from first when larger", () => {
    const a = new ContiguousCert(0, 10, integerWitness);
    const b = new ContiguousCert(2, 5, integerWitness);
    const merged = ContiguousCert.mergeContiguous([a, b]);
    const only = merged[0] as ContiguousCert<number>;
    expect(only.max).toBe(10);
  });

  test("mergeContiguous handles empty input", () => {
    expect(ContiguousCert.mergeContiguous<number>([])).toEqual([]);
  });

  test("mergeRanges branch coverage for min/max selection", () => {
    const mergeRanges = (ContiguousCert as any).mergeRanges as <T>(
      a: ContiguousCert<T>,
      b: ContiguousCert<T>
    ) => ContiguousCert<T>;
    const pickA = mergeRanges(new ContiguousCert(0, 5, integerWitness), new ContiguousCert(1, 4, integerWitness));
    expect(pickA.min).toBe(0);
    expect(pickA.max).toBe(5);
    const pickB = mergeRanges(new ContiguousCert(5, 6, integerWitness), new ContiguousCert(1, 10, integerWitness));
    expect(pickB.min).toBe(1);
    expect(pickB.max).toBe(10);
  });
});

