import { certNormalizer } from "@/domain/cert/CertNormalizer";
import { ContiguousCert, FiniteCert, UnionCert } from "@/index";
import { integerWitness } from "../../helpers";

describe("UnionCert", () => {
  const left = new ContiguousCert(0, 5, integerWitness);
  const right = new ContiguousCert(6, 10, integerWitness);

  test("normalize merges adjacent/overlapping contiguous ranges", () => {
    const union = new UnionCert(left, right);
    const normalized = certNormalizer.normalize(union);
    expect(normalized).toBeInstanceOf(ContiguousCert);
    if (normalized instanceof ContiguousCert) {
      expect(normalized.min).toBe(0);
      expect(normalized.max).toBe(10);
    }
  });

  test("encapsulates requires both branches to cover target", () => {
    const union = new UnionCert(left, right);
    const sub = new ContiguousCert(1, 4, integerWitness);
    expect(union.encapsulates(sub)).toBe(false); // each arm alone doesn't cover entire sub
    const pointSet = new FiniteCert([1, 7]);
    expect(union.encapsulates(pointSet)).toBe(false);
  });

  test("encapsulates union equality and empty", () => {
    const union = new UnionCert(left, right);
    const same = new UnionCert(left, right);
    expect(union.encapsulates(same)).toBe(true);
    expect(union.encapsulates(new FiniteCert([]))).toBe(true);
  });

  test("normalize handles empty unions", () => {
    const empty = new FiniteCert<number>([]);
    const union = new UnionCert(empty, empty);
    const normalized = certNormalizer.normalize(union);
    expect(normalized.isEmpty()).toBe(true);
  });

  test("normalize flattens nested unions", () => {
    const nested = new UnionCert(new UnionCert(left, right), new FiniteCert([]));
    const normalized = certNormalizer.normalize(nested);
    expect(normalized instanceof ContiguousCert).toBe(true);
    if (normalized instanceof ContiguousCert) {
      expect(normalized.min).toBe(0);
      expect(normalized.max).toBe(10);
    }
  });

  test("encapsulates union of swapped arms (order-insensitive coverage)", () => {
    const union = new UnionCert(left, right);
    const swapped = new UnionCert(right, left);
    // Conservative logic requires both branches independently cover targets; swapped order fails that.
    expect(union.encapsulates(swapped)).toBe(false);
  });

  test("encapsulates conservative false when only one branch covers", () => {
    const union = new UnionCert(left, right);
    const target = new ContiguousCert(0, 4, integerWitness); // covered by left only
    expect(union.encapsulates(target)).toBe(false);
  });

  test("normalize retains union when witnesses differ", () => {
    const otherWitness = {
      id: "other",
      compare: (a: number, b: number) => a - b,
      succ: (x: number) => x + 1,
      pred: (x: number) => x - 1
    };
    const a = new ContiguousCert(0, 2, integerWitness);
    const b = new ContiguousCert(0, 2, otherWitness);
    const union = new UnionCert(a, b);
    const normalized = certNormalizer.normalize(union);
    expect(normalized instanceof UnionCert).toBe(true);
  });

  test("contains covers left or right branches", () => {
    const union = new UnionCert(left, right);
    expect(union.contains(1)).toBe(true);
    expect(union.contains(9)).toBe(true);
    expect(union.contains(20)).toBe(false);
  });

  test("encapsulates union where both arms cover sub-union", () => {
    const sup = new UnionCert(new ContiguousCert(0, 10, integerWitness), new ContiguousCert(20, 30, integerWitness));
    const sub = new UnionCert(new ContiguousCert(1, 2, integerWitness), new ContiguousCert(22, 23, integerWitness));
    // Conservative rule still returns false because each arm must independently cover the target.
    expect(sup.encapsulates(sub)).toBe(false);
  });

  test("encapsulates other union when both branches individually cover", () => {
    const wideLeft = new ContiguousCert(0, 10, integerWitness);
    const wideRight = new ContiguousCert(0, 10, integerWitness);
    const sup = new UnionCert(wideLeft, wideRight);
    const sub = new UnionCert(new ContiguousCert(1, 2, integerWitness), new ContiguousCert(3, 4, integerWitness));
    expect(sup.encapsulates(sub)).toBe(true);
  });

  test("encapsulates returns true for identical union", () => {
    const union = new UnionCert(left, right);
    expect(union.encapsulates(union)).toBe(true);
  });

  test("isEmpty reflects children", () => {
    const empty = new FiniteCert<number>([]);
    const unionEmpty = new UnionCert(empty, empty);
    expect(unionEmpty.isEmpty()).toBe(true);
    const nonEmpty = new UnionCert(left, empty);
    expect(nonEmpty.isEmpty()).toBe(false);
  });

  test("normalize merges adjacent ranges to single contiguous", () => {
    const a = new ContiguousCert(0, 5, integerWitness);
    const b = new ContiguousCert(6, 10, integerWitness);
    const union = new UnionCert(a, b);
    const normalized = certNormalizer.normalize(union);
    expect(normalized instanceof ContiguousCert).toBe(true);
  });

  test("serialize nests child certs", () => {
    const union = new UnionCert(left, right, "uid");
    const serialized = union.serialize();
    expect(serialized.kind).toBe("union");
    expect(serialized.id).toBe("uid");
    expect(serialized.left.kind).toBe("contiguous");
    expect(serialized.right.kind).toBe("contiguous");
  });
});

