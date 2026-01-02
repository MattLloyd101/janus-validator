import { QuantifierDomain } from "@/domains/QuantifierDomain";
import { FiniteDomain } from "@/domains/FiniteDomain";

describe("QuantifierDomain", () => {
  it("enforces length and element domain", () => {
    const domain = new QuantifierDomain(new FiniteDomain(["x", "y"]), { min: 1, max: 2 });
    expect(domain.contains([])).toBe(false);
    expect(domain.contains(["x"])).toBe(true);
    expect(domain.contains(["x", "y"])).toBe(true);
    expect(domain.contains(["x", "z"])).toBe(false);
    expect(domain.contains(["x", "y", "x"])).toBe(false);
  });

  it("throws on invalid bounds", () => {
    expect(() => new QuantifierDomain(new FiniteDomain([1]), { min: 2, max: 1 })).toThrow(
      "Quantifier max must be >= min"
    );
  });

  it("allows unbounded max", () => {
    const domain = new QuantifierDomain(new FiniteDomain([1]), { min: 0 });
    expect(domain.contains([1, 1, 1, 1, 1])).toBe(true);
  });

  it("rejects elements outside inner domain", () => {
    const domain = new QuantifierDomain(new FiniteDomain([1]), { min: 0, max: 3 });
    expect(domain.contains([2])).toBe(false);
  });

  it("normalize clones inner domain", () => {
    const domain = new QuantifierDomain(new FiniteDomain([1]), { min: 0, max: 1 });
    const norm = domain.normalize() as QuantifierDomain<number>;
    expect(norm).not.toBe(domain);
    expect(norm.inner).not.toBe(domain.inner);
    expect(norm.contains([1])).toBe(true);
  });

  it("rejects arrays longer than max", () => {
    const domain = new QuantifierDomain(new FiniteDomain([1]), { min: 0, max: 2 });
    expect(domain.contains([1, 1, 1])).toBe(false);
  });

  it("rejects non-array inputs", () => {
    const domain = new QuantifierDomain(new FiniteDomain([1]), { min: 0, max: 2 });
    expect(domain.contains("not-array" as any)).toBe(false);
  });
});

