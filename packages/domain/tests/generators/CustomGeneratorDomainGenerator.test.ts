import { CustomGeneratorDomain } from "@/domains/CustomGeneratorDomain";
import { CustomGeneratorDomainGenerator } from "@/generators/CustomGeneratorDomainGenerator";
import { FiniteDomain } from "@/domains/FiniteDomain";
import { rngFromSequence } from "./helpers";

describe("CustomGeneratorDomainGenerator", () => {
  it("delegates to custom generate", () => {
    const inner = new FiniteDomain([1, 2, 3]);
    const custom = new CustomGeneratorDomain(inner, () => 42);
    const gen = new CustomGeneratorDomainGenerator<number>();
    const rng = rngFromSequence([0.1]);
    expect(gen.generate(custom, rng)).toBe(42);
  });
});
