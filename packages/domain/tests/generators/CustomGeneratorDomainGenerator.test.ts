import { CustomGeneratorDomain } from "@/domains/CustomGeneratorDomain";
import { CustomGeneratorDomainGenerator } from "@/generators/CustomGeneratorDomainGenerator";
import { rngFromSequence } from "./helpers";

describe("CustomGeneratorDomainGenerator", () => {
  it("delegates to custom generate", () => {
    const custom = new CustomGeneratorDomain<number>({ contains: () => true, kind: 0 as any } as any, () => 42);
    const gen = new CustomGeneratorDomainGenerator<number>();
    const rng = rngFromSequence([0.1]);
    expect(gen.generate(custom, rng)).toBe(42);
  });
});

