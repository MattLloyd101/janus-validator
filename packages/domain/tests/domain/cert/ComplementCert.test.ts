import { ComplementCert, ContiguousCert, FiniteCert } from "@/index";
import { integerWitness } from "../../helpers";

describe("ComplementCert", () => {
  const universe = new ContiguousCert(0, 10, integerWitness);

  test("contains negates inner", () => {
    const inner = new FiniteCert([1, 2]);
    const complement = new ComplementCert(inner);
    expect(complement.contains(1)).toBe(false);
    expect(complement.contains(5)).toBe(true);
  });

  test("encapsulates trivially accepts empty and equality", () => {
    const inner = new FiniteCert<number>([]);
    const complement = new ComplementCert(inner);
    expect(complement.encapsulates(new ComplementCert(inner))).toBe(true);
    expect(complement.encapsulates(new FiniteCert([]))).toBe(true);
    expect(complement.encapsulates(new ComplementCert(new FiniteCert([])))).toBe(true);
  });

  test("contains returns false without universe and encapsulates conservative false", () => {
    const inner = new FiniteCert([1]);
    const complement = new ComplementCert(inner);
    expect(complement.contains(1)).toBe(false);
    expect(complement.encapsulates(new FiniteCert([2]))).toBe(false);
  });

  test("encapsulates returns true when equals universe parameter", () => {
    const inner = new FiniteCert([1]);
    const complement = new ComplementCert(inner);
    expect(complement.encapsulates(new ComplementCert(inner))).toBe(true);
  });

  test("encapsulates returns false when universe provided but not equal", () => {
    const inner = new FiniteCert([1]);
    const complement = new ComplementCert(inner);
    const universe = new ComplementCert(new FiniteCert([2]));
    expect(complement.encapsulates(new FiniteCert([3]))).toBe(false);
  });

  test("contains blocks inner values", () => {
    const inner = new FiniteCert([1]);
    const complement = new ComplementCert(inner);
    expect(complement.contains(1)).toBe(false);
  });

  test("normalize returns new complement", () => {
    const inner = new FiniteCert([1]);
    const complement = new ComplementCert(inner);
    const normalized = complement.normalize();
    expect(normalized.contains(1)).toBe(false);
  });

  test("encapsulates returns true for exact same complement", () => {
    const inner = new FiniteCert([1]);
    const complement = new ComplementCert(inner);
    expect(complement.encapsulates(complement)).toBe(true);
  });

  test("isEmpty is always false", () => {
    const complement = new ComplementCert(new FiniteCert([1]));
    expect(complement.isEmpty()).toBe(false);
  });

  test("contains returns true when not in inner", () => {
    const inner = new FiniteCert([1]);
    const complement = new ComplementCert(inner);
    expect(complement.contains(99)).toBe(true);
  });

  test("withWitness rewraps inner", () => {
    const inner = new FiniteCert([1]);
    const complement = new ComplementCert(inner);
    const otherWitness = {
      compare: (a: number, b: number) => a - b,
      succ: (x: number) => x + 1,
      pred: (x: number) => x - 1
    };
    const rewritten = complement.withWitness(otherWitness as any);
    expect(rewritten.hash()).toContain("complement");
  });
});

