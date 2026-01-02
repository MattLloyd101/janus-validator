import { BigIntDomain } from "@/domains/BigIntDomain";

describe("BigIntDomain", () => {
  it("contains bigints in inclusive range", () => {
    const domain = new BigIntDomain(0n, 5n);
    expect(domain.contains(-1n)).toBe(false);
    expect(domain.contains(0n)).toBe(true);
    expect(domain.contains(5n)).toBe(true);
    expect(domain.contains(6n)).toBe(false);
  });
});

