import { certNormalizer } from "@/domain/cert/CertNormalizer";
import { FiniteCert } from "@/index";

describe("FiniteCert", () => {
  test("contains and isEmpty", () => {
    const cert = new FiniteCert([1, 2, 3]);
    expect(cert.contains(2)).toBe(true);
    expect(cert.contains(4)).toBe(false);
    expect(cert.isEmpty()).toBe(false);
    expect(new FiniteCert([]).isEmpty()).toBe(true);
  });

  test("encapsulates finite subsets", () => {
    const sup = new FiniteCert([1, 2, 3]);
    const sub = new FiniteCert([1, 2]);
    const diff = new FiniteCert([4]);
    expect(sup.encapsulates(sub)).toBe(true);
    expect(sup.encapsulates(diff)).toBe(false);
  });

  test("normalize, withWitness, equals/hash are stable", () => {
    const cert = new FiniteCert([1, 2]);
    const normalized = certNormalizer.normalize(cert);
    expect(normalized).toBe(cert);
    const withWitness = cert.withWitness({ id: "noop", compare: () => 0, succ: () => undefined, pred: () => undefined });
    expect(withWitness).toBe(cert);
    const same = new FiniteCert([1, 2]);
    expect(cert.equals(same)).toBe(true);
    const different = new FiniteCert([2, 3]);
    expect(cert.equals(different)).toBe(false);
  });

  test("serialize produces finite shape", () => {
    const cert = new FiniteCert([1, 2], "fid");
    const serialized = cert.serialize();
    expect(serialized).toEqual({ kind: "finite", id: "fid", values: [1, 2] });
  });

  test("encapsulates returns false for non-finite", () => {
    const sup = new FiniteCert([1, 2, 3]);
    const nonFinite = { contains: () => true, isEmpty: () => false } as any;
    expect(sup.encapsulates(nonFinite as any)).toBe(false);
  });

  test("encapsulates empty sup branches", () => {
    const emptySup = new FiniteCert<number>([]);
    expect(emptySup.encapsulates(new FiniteCert([]))).toBe(true);
    expect(emptySup.encapsulates(new FiniteCert([1]))).toBe(false);
  });
});

