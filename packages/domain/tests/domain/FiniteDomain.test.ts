import { FiniteDomain } from "@/domains/FiniteDomain";

describe("FiniteDomain", () => {
  it("contains exactly its elements", () => {
    const domain = new FiniteDomain([1, 2, 3]);
    expect(domain.contains(2)).toBe(true);
    expect(domain.contains(4)).toBe(false);
  });

  it("dedupes values at construction (normalized on create)", () => {
    const domain = new FiniteDomain([1, 1, 2]);
    expect(domain.contains(1)).toBe(true);
    expect(domain.contains(3)).toBe(false);
    expect(domain.size).toBe(2);
  });
});
