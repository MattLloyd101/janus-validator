import { CustomGeneratorDomain } from "@/domains/CustomGeneratorDomain";
import { FiniteDomain } from "@/domains/FiniteDomain";

describe("CustomGeneratorDomain", () => {
  it("delegates contains to inner domain", () => {
    const inner = new FiniteDomain([1, 2, 3]);
    const domain = new CustomGeneratorDomain(inner, () => 1);
    expect(domain.contains(1)).toBe(true);
    expect(domain.contains(4)).toBe(false);
  });
});
