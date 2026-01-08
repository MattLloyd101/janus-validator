import { ContiguousDomain } from "@/domains/ContiguousDomain";

describe("ContiguousDomain", () => {
  it("validates numbers within range", () => {
    const domain = new ContiguousDomain(0, 100);
    expect(domain.contains(50)).toBe(true);
    expect(domain.contains(0)).toBe(true);
    expect(domain.contains(100)).toBe(true);
    expect(domain.contains(-1)).toBe(false);
    expect(domain.contains(101)).toBe(false);
  });

  it("rejects non-number values", () => {
    const domain = new ContiguousDomain(0, 100);
    // Testing defensive behavior
    expect(domain.contains("50")).toBe(false);
    expect(domain.contains(null)).toBe(false);
  });

  it("accepts floats within range (no integer-only mode)", () => {
    // ContiguousDomain now accepts any number within range (integers or floats)
    const domain = new ContiguousDomain(0, 10);
    expect(domain.contains(5)).toBe(true);
    expect(domain.contains(5.5)).toBe(true);
    expect(domain.contains(0.1)).toBe(true);
    expect(domain.contains(9.9)).toBe(true);
  });

  it("throws when min > max", () => {
    expect(() => new ContiguousDomain(100, 0)).toThrow("ContiguousDomain min must be <= max");
  });

  it("handles bigint domains", () => {
    const domain = new ContiguousDomain(0n, 100n);
    expect(domain.contains(50n)).toBe(true);
    expect(domain.contains(0n)).toBe(true);
    expect(domain.contains(100n)).toBe(true);
    expect(domain.contains(-1n)).toBe(false);
    expect(domain.contains(101n)).toBe(false);
    // Rejects non-bigint when domain is bigint
    expect(domain.contains(50)).toBe(false);
  });
});
