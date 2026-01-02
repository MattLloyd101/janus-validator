import { CustomGeneratorDomain } from "@/domains/CustomGeneratorDomain";

describe("CustomGeneratorDomain", () => {
  it("delegates contains to inner domain", () => {
    const inner = { contains: (v: unknown) => v === 1, kind: 0 as any };
    const domain = new CustomGeneratorDomain<number>(inner as any, () => 1);
    expect(domain.contains(1)).toBe(true);
    expect(domain.contains(2)).toBe(false);
  });
});

