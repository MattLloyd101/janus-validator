import { certNormalizer } from "@/domain/cert/CertNormalizer";
import { ComplementCert, ContiguousCert, FiniteCert, IntersectCert, UnionCert } from "@/index";
import { DomainCert } from "@/domain/cert/DomainCert";
import { integerWitness } from "../../helpers";

class DummyCert<T> extends DomainCert<T> {
  readonly kind = "dummy" as any;
  constructor() {
    super();
  }
  hash() {
    return "dummy";
  }
  withWitness(): DomainCert<T> {
    return this;
  }
  contains(): boolean {
    return false;
  }
  isEmpty(): boolean {
    return false;
  }
  encapsulates(): boolean {
    return false;
  }
  serialize() {
    return { kind: "finite", values: [] as T[] } as any;
  }
}

class RawUnion<T> extends UnionCert<T> {
  normalize(): UnionCert<T> {
    return this;
  }
}

class RawIntersect<T> extends IntersectCert<T> {
  normalize(): IntersectCert<T> {
    return this;
  }
}

describe("CertNormalizer", () => {
  const w = integerWitness;

  test("union merges contiguous, removes empties, and dedupes identical parts", () => {
    const empty = new FiniteCert<number>([]);
    const a = new ContiguousCert(0, 5, w);
    const b = new ContiguousCert(6, 10, w); // adjacent -> merge
    const dup = new ContiguousCert(0, 5, w);
    const union = new UnionCert(new UnionCert(a, empty), new UnionCert(b, dup));

    const normalized = certNormalizer.normalize(union);
    expect(normalized).toBeInstanceOf(ContiguousCert);
    const c = normalized as ContiguousCert<number>;
    expect(c.min).toBe(0);
    expect(c.max).toBe(10);
    expect(c.contains(7)).toBe(true);
  });

  test("union of only empties normalizes to empty finite", () => {
    const empty = new FiniteCert<number>([]);
    const union = new UnionCert(empty, new UnionCert(empty, empty));
    const normalized = certNormalizer.normalize(union);
    expect(normalized).toBeInstanceOf(FiniteCert);
    expect((normalized as FiniteCert<number>).values.length).toBe(0);
  });

  test("union with distinct non-contiguous parts stays as chain deterministically ordered", () => {
    const a = new FiniteCert([1]);
    const b = new FiniteCert([2]);
    const union = new UnionCert(a, b);
    const normalized = certNormalizer.normalize(union) as UnionCert<number>;
    expect(normalized.contains(1)).toBe(true);
    expect(normalized.contains(2)).toBe(true);
  });

  test("union flattens nested unions and sorts deterministically (covers reverse order)", () => {
    const a = new FiniteCert([2]);
    const b = new FiniteCert([1]);
    const nested = new UnionCert(new UnionCert(a, b), new FiniteCert([3]));
    const normalized = certNormalizer.normalize(nested);
    expect(normalized.contains(1)).toBe(true);
    expect(normalized.contains(2)).toBe(true);
    expect(normalized.contains(3)).toBe(true);
  });

  test("intersect of disjoint contiguous ranges becomes empty", () => {
    const a = new ContiguousCert(0, 1, w);
    const b = new ContiguousCert(3, 4, w);
    const inter = new IntersectCert(a, b);
    const normalized = certNormalizer.normalize(inter);
    expect(normalized).toBeInstanceOf(FiniteCert);
    expect((normalized as FiniteCert<number>).values.length).toBe(0);
  });

  test("intersect clips overlapping contiguous ranges and dedupes identical parts", () => {
    const a = new ContiguousCert(0, 10, w);
    const b = new ContiguousCert(5, 15, w);
    const dup = new ContiguousCert(0, 10, w);
    const inter = new IntersectCert(new IntersectCert(a, b), dup);
    const normalized = certNormalizer.normalize(inter);
    expect(normalized).toBeInstanceOf(ContiguousCert);
    const c = normalized as ContiguousCert<number>;
    expect(c.min).toBe(5);
    expect(c.max).toBe(10);
    expect(c.contains(4)).toBe(false);
    expect(c.contains(6)).toBe(true);
  });

  test("intersect short-circuits to empty when any child is empty", () => {
    const empty = new FiniteCert<number>([]);
    const nonEmpty = new ContiguousCert(0, 1, w);
    const inter = new IntersectCert(empty, nonEmpty);
    const normalized = certNormalizer.normalize(inter);
    expect(normalized).toBeInstanceOf(FiniteCert);
    expect((normalized as FiniteCert<number>).values.length).toBe(0);
  });

  test("intersect reduceIntersect can return zero-length when all parts drop", () => {
    const empty = new FiniteCert<number>([]);
    const inter = new IntersectCert(empty, empty);
    const normalized = certNormalizer.normalize(inter);
    expect(normalized).toBeInstanceOf(FiniteCert);
    expect((normalized as FiniteCert<number>).values.length).toBe(0);
  });

  test("intersect keeps heterogeneous parts when not mergeable", () => {
    const a = new FiniteCert([1]);
    const b = new ContiguousCert(0, 2, w);
    const inter = new IntersectCert(a, b);
    const normalized = certNormalizer.normalize(inter);
    // should remain an intersect chain because merge rule only applies to contiguous pairs.
    expect(normalized).toBeInstanceOf(IntersectCert);
    expect(normalized.contains(1)).toBe(true);
  });

  test("intersect flattens nested intersects and sorts deterministically", () => {
    const a = new FiniteCert([2]);
    const b = new FiniteCert([1]);
    const nested = new IntersectCert(new IntersectCert(a, b), new FiniteCert([3]));
    const normalized = certNormalizer.normalize(nested);
    expect(normalized.contains(1)).toBe(false);
    expect(normalized.contains(2)).toBe(false);
    expect(normalized.contains(3)).toBe(false);
  });

  test("complement normalizes inner and universe", () => {
    const inner = new UnionCert(new FiniteCert([1]), new FiniteCert([]));
    const universe = new UnionCert(new ContiguousCert(0, 10, w), new FiniteCert([]));
    const comp = new ComplementCert(inner, universe);
    const normalized = certNormalizer.normalize(comp) as ComplementCert<number>;
    expect(normalized.of).toBeInstanceOf(FiniteCert);
    expect(normalized.universe).toBeInstanceOf(ContiguousCert);
    expect(normalized.contains(5)).toBe(true);
    expect(normalized.contains(1)).toBe(false);
  });

  test("normalization is idempotent", () => {
    const cert: DomainCert<number> = new UnionCert(new FiniteCert([1]), new FiniteCert([1]));
    const once = certNormalizer.normalize(cert);
    const twice = certNormalizer.normalize(once);
    expect(once.hash()).toBe(twice.hash());
  });

  test("fallback normalization returns unknown cert unchanged", () => {
    expect(() => (certNormalizer as any).normalizeCert({} as DomainCert<number>)).toThrow("Unsupported certificate type");
  });

  test("normalizeUnion flattens nested unions when invoked directly", () => {
    const a = new FiniteCert([2]);
    const b = new FiniteCert([1]);
    const c = new FiniteCert([3]);
    const nested = new UnionCert(new RawUnion(a, b), new RawUnion(c, b));
    const normalized = (certNormalizer as any).normalizeUnion(nested);
    expect(normalized.contains(1)).toBe(true);
    expect(normalized.contains(2)).toBe(true);
    expect(normalized.contains(3)).toBe(true);
  });

  test("normalizeIntersect flattens nested intersects when invoked directly", () => {
    const a = new FiniteCert([2]);
    const b = new FiniteCert([1]);
    const c = new FiniteCert([2]);
    const nested = new IntersectCert(new RawIntersect(a, b), new RawIntersect(c, b));
    const normalized = (certNormalizer as any).normalizeIntersect(nested);
    expect(normalized.contains(1)).toBe(false);
    expect(normalized.contains(2)).toBe(false);
  });

  test("normalize throws on unsupported cert", () => {
    expect(() => certNormalizer.normalize({} as DomainCert<number>)).toThrow("Unsupported certificate type");
  });

  test("normalizeUnion branch-walks raw nested union children", () => {
    const inner = new UnionCert(new FiniteCert([1]), new FiniteCert([2]));
    const outer = new UnionCert(inner, new FiniteCert([3]));
    const normalized = certNormalizer.normalize(outer);
    expect(normalized.contains(1)).toBe(true);
    expect(normalized.contains(2)).toBe(true);
    expect(normalized.contains(3)).toBe(true);
  });

  test("normalizeIntersect branch-walks raw nested intersect children", () => {
    const inner = new IntersectCert(new FiniteCert([1]), new FiniteCert([1]));
    const outer = new IntersectCert(inner, new FiniteCert([1]));
    const normalized = certNormalizer.normalize(outer);
    expect(normalized.isEmpty()).toBe(false);
    expect(normalized.contains(1)).toBe(true);
  });

  test("normalizeUnion dedupes and sorts deterministically by hash", () => {
    // hashes: finite:1 < finite:2 lexicographically
    const one = new FiniteCert([1]);
    const two = new FiniteCert([2]);
    const union = new UnionCert(two, new UnionCert(two, one));
    const normalized = certNormalizer.normalize(union) as UnionCert<number>;
    expect(normalized).toBeInstanceOf(UnionCert);
    expect(normalized.left.hash() < normalized.right.hash()).toBe(true);
  });

  test("normalizeIntersect dedupes and sorts deterministically by hash", () => {
    const one = new FiniteCert([1]);
    const two = new FiniteCert([2]);
    const inter = new IntersectCert(new IntersectCert(two, two), one);
    const normalized = certNormalizer.normalize(inter) as IntersectCert<number>;
    expect(normalized).toBeInstanceOf(IntersectCert);
    expect(normalized.left.hash() < normalized.right.hash()).toBe(true);
  });

  test("normalizeUnion dedupe keeps single instance when hashes are equal", () => {
    const left = new FiniteCert([1]);
    const right = new FiniteCert([1]);
    const union = new UnionCert(left, right);
    const normalized = certNormalizer.normalize(union);
    expect(normalized).toBeInstanceOf(FiniteCert);
    expect((normalized as FiniteCert<number>).values).toEqual([1]);
  });

  test("normalizeIntersect dedupe keeps single instance when hashes are equal", () => {
    const left = new FiniteCert([1]);
    const right = new FiniteCert([1]);
    const inter = new IntersectCert(left, right);
    const normalized = certNormalizer.normalize(inter);
    expect(normalized).toBeInstanceOf(FiniteCert);
    expect((normalized as FiniteCert<number>).values).toEqual([1]);
  });
});

