import { QuantifierDomain } from "@/domains/QuantifierDomain";
import { FiniteDomain } from "@/domains/FiniteDomain";

describe("QuantifierDomain", () => {
  it("validates arrays within count range", () => {
    const inner = new FiniteDomain([1, 2, 3]);
    const domain = new QuantifierDomain(inner, { min: 1, max: 3 });
    expect(domain.contains([1])).toBe(true);
    expect(domain.contains([1, 2, 3])).toBe(true);
    expect(domain.contains([])).toBe(false);
    expect(domain.contains([1, 2, 3, 1])).toBe(false);
  });

  it("validates all elements against inner domain", () => {
    const inner = new FiniteDomain([1, 2]);
    const domain = new QuantifierDomain(inner, { min: 1, max: 5 });
    expect(domain.contains([1, 2, 1])).toBe(true);
    expect(domain.contains([1, 3])).toBe(false);
  });

  it("rejects non-array values", () => {
    const inner = new FiniteDomain([1]);
    const domain = new QuantifierDomain(inner, { min: 0, max: 10 });
    // Testing defensive behavior
    expect(domain.contains("not-array")).toBe(false);
  });

  it("throws when min < 0", () => {
    const inner = new FiniteDomain([1]);
    expect(() => new QuantifierDomain(inner, { min: -1 })).toThrow("Quantifier min must be >= 0");
  });

  it("throws when max < min", () => {
    const inner = new FiniteDomain([1]);
    expect(() => new QuantifierDomain(inner, { min: 5, max: 3 })).toThrow("Quantifier max must be >= min");
  });
});
