import { certNormalizer } from "@/domain/cert/CertNormalizer";
import { ComplementCert, ContiguousCert, FiniteCert } from "@/index";
import { integerWitness } from "../../helpers";

describe("ComplementCert", () => {
  const universe = new ContiguousCert(0, 100, integerWitness);

  test("contains negates inner within universe", () => {
    const inner = new FiniteCert([1, 2]);
    const complement = new ComplementCert(inner, universe);
    expect(complement.contains(1)).toBe(false);
    expect(complement.contains(5)).toBe(true);
  });

  test("encapsulates trivially accepts empty and equality", () => {
    const inner = new FiniteCert<number>([]);
    const complement = new ComplementCert(inner, universe);
    expect(complement.encapsulates(new ComplementCert(inner, universe))).toBe(true);
    expect(complement.encapsulates(new FiniteCert([]))).toBe(true);
    expect(complement.encapsulates(new ComplementCert(new FiniteCert([]), universe))).toBe(true);
  });

  test("contains returns false without universe membership and encapsulates conservative false", () => {
    const inner = new FiniteCert([1]);
    const complement = new ComplementCert(inner, universe);
    expect(complement.contains(1)).toBe(false);
    expect(complement.encapsulates(new FiniteCert([2]))).toBe(false);
  });

  test("encapsulates returns true when equals universe parameter", () => {
    const inner = new FiniteCert([1]);
    const complement = new ComplementCert(inner, universe);
    expect(complement.encapsulates(new ComplementCert(inner, universe))).toBe(true);
  });

  test("encapsulates returns false when universes differ", () => {
    const inner = new FiniteCert([1]);
    const complement = new ComplementCert(inner, universe);
    const otherUniverse = new ContiguousCert(0, 50, integerWitness);
    const otherComplement = new ComplementCert(new FiniteCert([2]), otherUniverse);
    expect(complement.encapsulates(otherComplement)).toBe(false);
  });

  test("encapsulates other complement only when universes match and inner covers", () => {
    const inner = new FiniteCert([1]);
    const broaderInner = new FiniteCert([1, 2]);
    const complement = new ComplementCert(inner, universe);
    const otherComplement = new ComplementCert(broaderInner, universe);
    expect(complement.encapsulates(otherComplement)).toBe(true);
  });

  test("contains blocks inner values", () => {
    const inner = new FiniteCert([1]);
    const complement = new ComplementCert(inner, universe);
    expect(complement.contains(1)).toBe(false);
  });

  test("normalize returns new complement", () => {
    const inner = new FiniteCert([1]);
    const complement = new ComplementCert(inner, universe);
    const normalized = certNormalizer.normalize(complement);
    expect(normalized.contains(1)).toBe(false);
  });

  test("encapsulates returns true for exact same complement", () => {
    const inner = new FiniteCert([1]);
    const complement = new ComplementCert(inner, universe);
    expect(complement.encapsulates(complement)).toBe(true);
  });

  test("isEmpty is always false", () => {
    const complement = new ComplementCert(new FiniteCert([1]), universe);
    expect(complement.isEmpty()).toBe(false);
  });

  test("contains returns true when not in inner but inside universe", () => {
    const inner = new FiniteCert([1]);
    const complement = new ComplementCert(inner, universe);
    expect(complement.contains(99)).toBe(true);
    expect(complement.contains(150)).toBe(false); // outside universe
  });

  test("withWitness rewraps inner and universe", () => {
    const inner = new FiniteCert([1]);
    const complement = new ComplementCert(inner, universe);
    const otherWitness = {
      compare: (a: number, b: number) => a - b,
      succ: (x: number) => x + 1,
      pred: (x: number) => x - 1
    };
    const rewritten = complement.withWitness(otherWitness as any);
    expect(rewritten.hash()).toContain("complement");
  });
});

