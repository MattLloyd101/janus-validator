import { FiniteDomain } from "@/domains/FiniteDomain";

describe("FiniteDomain", () => {
  it("contains exactly its elements", () => {
    const domain = new FiniteDomain([1, 2, 3]);
    expect(domain.contains(2)).toBe(true);
    expect(domain.contains(4)).toBe(false);
  });

  it("normalize preserves values", () => {
    const domain = new FiniteDomain([1, 2]);
    const normalized = domain.normalize() as FiniteDomain<number>;
    expect(normalized.contains(1)).toBe(true);
    expect(normalized.contains(3)).toBe(false);
    expect(normalized.size).toBe(2);
  });
});
