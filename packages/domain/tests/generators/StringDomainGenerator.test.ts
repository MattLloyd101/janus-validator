import { StringDomain } from "@/domains/StringDomain";
import { StringDomainGenerator } from "@/generators/StringDomainGenerator";
import { rngFromSequence } from "./helpers";

describe("StringDomainGenerator", () => {
  it("respects min/max lengths", () => {
    const gen = new StringDomainGenerator();
    const domain = new StringDomain({ minLength: 2, maxLength: 4 });
    const rng = rngFromSequence([0.1, 0.9, 0.5]);
    const value = gen.generate(domain, rng);
    expect(value.length).toBeGreaterThanOrEqual(2);
    expect(value.length).toBeLessThanOrEqual(4);
  });
});

