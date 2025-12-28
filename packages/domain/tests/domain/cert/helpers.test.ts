import { FiniteCert, ContiguousCert, UnionCert, IntersectCert, ComplementCert } from "@/index";
import { isFiniteCert, isContiguousCert, isUnionCert, isIntersectCert, isComplementCert } from "@/domain/cert/helpers";
import { integerWitness } from "../../helpers";

describe("helpers type guards", () => {
  test("isFiniteCert", () => {
    expect(isFiniteCert(new FiniteCert([]))).toBe(true);
    expect(isFiniteCert(new ContiguousCert(0, 1, integerWitness))).toBe(false);
  });

  test("isContiguousCert", () => {
    expect(isContiguousCert(new ContiguousCert(0, 1, integerWitness))).toBe(true);
    expect(isContiguousCert(new FiniteCert([]))).toBe(false);
  });

  test("isUnionCert", () => {
    const union = new UnionCert(new FiniteCert([1]), new FiniteCert([2]));
    expect(isUnionCert(union)).toBe(true);
    expect(isUnionCert(new FiniteCert([]))).toBe(false);
  });

  test("isIntersectCert", () => {
    const inter = new IntersectCert(new FiniteCert([1]), new FiniteCert([2]));
    expect(isIntersectCert(inter)).toBe(true);
    expect(isIntersectCert(new FiniteCert([]))).toBe(false);
  });

  test("isComplementCert", () => {
    const universe = new ContiguousCert(0, 10, integerWitness);
    const comp = new ComplementCert(new FiniteCert([1]), universe);
    expect(isComplementCert(comp)).toBe(true);
    expect(isComplementCert(new FiniteCert([]))).toBe(false);
  });
});

