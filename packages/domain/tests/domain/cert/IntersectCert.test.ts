import { ContiguousCert, IntersectCert, FiniteCert } from "@/index";
import { integerWitness } from "../../helpers";

describe("IntersectCert", () => {
  test("normalize disjoint contiguous to empty finite", () => {
    const a = new ContiguousCert(0, 2, integerWitness);
    const b = new ContiguousCert(5, 7, integerWitness);
    const inter = new IntersectCert(a, b);
    const normalized = inter.normalize();
    expect(normalized.isEmpty()).toBe(true);
  });

  test("encapsulates requires both branches to cover target", () => {
    const a = new ContiguousCert(0, 5, integerWitness);
    const b = new ContiguousCert(3, 7, integerWitness);
    const inter = new IntersectCert(a, b);
    const sub = new ContiguousCert(3, 5, integerWitness);
    expect(inter.encapsulates(sub)).toBe(true);
    const wider = new ContiguousCert(1, 6, integerWitness);
    expect(inter.encapsulates(wider)).toBe(false);
  });

  test("encapsulates equals and empty", () => {
    const a = new ContiguousCert(0, 5, integerWitness);
    const b = new ContiguousCert(3, 7, integerWitness);
    const inter = new IntersectCert(a, b);
    const same = new IntersectCert(a, b);
    expect(inter.encapsulates(same)).toBe(true);
    expect(inter.encapsulates(new FiniteCert([]))).toBe(true);
  });

  test("normalize collapses identical ranges", () => {
    const a = new ContiguousCert(0, 5, integerWitness);
    const b = new ContiguousCert(0, 5, integerWitness);
    const inter = new IntersectCert(a, b);
    const normalized = inter.normalize();
    expect(normalized instanceof ContiguousCert).toBe(true);
    if (normalized instanceof ContiguousCert) {
      expect(normalized.min).toBe(0);
      expect(normalized.max).toBe(5);
    }
  });

  test("normalize flattens nested intersects", () => {
    const a = new ContiguousCert(0, 5, integerWitness);
    const b = new ContiguousCert(3, 10, integerWitness);
    const nested = new IntersectCert(new IntersectCert(a, b), a);
    const normalized = nested.normalize();
    expect(normalized instanceof ContiguousCert).toBe(true);
    if (normalized instanceof ContiguousCert) {
      expect(normalized.min).toBe(3);
      expect(normalized.max).toBe(5);
    }
  });

  test("encapsulates intersect of swapped arms", () => {
    const a = new ContiguousCert(0, 5, integerWitness);
    const b = new ContiguousCert(3, 7, integerWitness);
    const inter = new IntersectCert(a, b);
    const swapped = new IntersectCert(b, a);
    // Conservative: each arm must cover the target; swapped order does not satisfy both.
    expect(inter.encapsulates(swapped)).toBe(false);
  });

  test("encapsulates conservative false when one arm fails", () => {
    const a = new ContiguousCert(0, 5, integerWitness);
    const b = new ContiguousCert(3, 7, integerWitness);
    const inter = new IntersectCert(a, b);
    const target = new ContiguousCert(0, 7, integerWitness);
    expect(inter.encapsulates(target)).toBe(false);
  });

  test("normalize returns chain when multiple parts remain", () => {
    const a = new ContiguousCert(0, 5, integerWitness);
    const b = new ContiguousCert(3, 10, integerWitness);
    const finite = new FiniteCert([4, 5]);
    const nested = new IntersectCert(new IntersectCert(a, b), finite);
    const normalized = nested.normalize();
    expect(normalized instanceof IntersectCert).toBe(true);
  });

  test("normalize short-circuits when part is empty", () => {
    const a = new ContiguousCert(0, 5, integerWitness);
    const empty = new FiniteCert<number>([]);
    const inter = new IntersectCert(a, empty);
    const normalized = inter.normalize();
    expect(normalized.isEmpty()).toBe(true);
  });

  test("encapsulates returns true for self", () => {
    const a = new ContiguousCert(0, 5, integerWitness);
    const b = new ContiguousCert(3, 7, integerWitness);
    const inter = new IntersectCert(a, b);
    expect(inter.encapsulates(inter)).toBe(true);
  });

  test("encapsulates intersect with both branches covering target", () => {
    const a = new ContiguousCert(0, 5, integerWitness);
    const b = new ContiguousCert(1, 4, integerWitness);
    const inter = new IntersectCert(a, b);
    const target = new ContiguousCert(2, 3, integerWitness);
    expect(inter.encapsulates(target)).toBe(true);
  });

  test("contains returns false when only one side matches", () => {
    const a = new ContiguousCert(0, 5, integerWitness);
    const b = new ContiguousCert(10, 20, integerWitness);
    const inter = new IntersectCert(a, b);
    expect(inter.contains(3)).toBe(false);
  });

  test("isEmpty reflects children", () => {
    const empty = new FiniteCert<number>([]);
    const inter = new IntersectCert(empty, empty);
    expect(inter.isEmpty()).toBe(true);
  });

  test("contains returns true when both sides match", () => {
    const a = new ContiguousCert(0, 5, integerWitness);
    const b = new ContiguousCert(2, 4, integerWitness);
    const inter = new IntersectCert(a, b);
    expect(inter.contains(3)).toBe(true);
  });

  test("normalize merges overlapping contiguous to single range", () => {
    const a = new ContiguousCert(0, 5, integerWitness);
    const b = new ContiguousCert(2, 6, integerWitness);
    const inter = new IntersectCert(a, b);
    const normalized = inter.normalize();
    expect(normalized instanceof ContiguousCert).toBe(true);
    if (normalized instanceof ContiguousCert) {
      expect(normalized.min).toBe(2);
      expect(normalized.max).toBe(5);
    }
  });

  test("encapsulates intersect with non-intersect other returns false", () => {
    const a = new ContiguousCert(0, 5, integerWitness);
    const b = new ContiguousCert(2, 4, integerWitness);
    const inter = new IntersectCert(a, b);
    const target = new ContiguousCert(0, 10, integerWitness);
    expect(inter.encapsulates(target)).toBe(false);
  });

  test("encapsulates other intersect when both branches cover", () => {
    const supLeft = new ContiguousCert(0, 10, integerWitness);
    const supRight = new ContiguousCert(0, 10, integerWitness);
    const subLeft = new ContiguousCert(1, 2, integerWitness);
    const subRight = new ContiguousCert(3, 4, integerWitness);
    const sup = new IntersectCert(supLeft, supRight);
    const sub = new IntersectCert(subLeft, subRight);
    expect(sup.encapsulates(sub)).toBe(true);
  });

  test("intersectRanges picks min/max from either side", () => {
    const a = new ContiguousCert(5, 15, integerWitness);
    const b = new ContiguousCert(1, 10, integerWitness);
    const inter = new IntersectCert(a, b);
    const normalized = inter.normalize();
    expect(normalized instanceof ContiguousCert).toBe(true);
    if (normalized instanceof ContiguousCert) {
      expect(normalized.min).toBe(5);
      expect(normalized.max).toBe(10);
    }
  });
});

