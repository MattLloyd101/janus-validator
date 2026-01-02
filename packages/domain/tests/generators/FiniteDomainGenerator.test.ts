import { FiniteDomain } from "@/domains/FiniteDomain";
import { FiniteDomainGenerator } from "@/generators/FiniteDomainGenerator";
import { rngFromSequence } from "./helpers";

describe("FiniteDomainGenerator", () => {
  it("picks an element from the finite set", () => {
    const gen = new FiniteDomainGenerator<number>();
    const domain = new FiniteDomain([1, 2, 3]);
    const rng = rngFromSequence([0.95]);
    expect(gen.generate(domain, rng)).toBe(3);
  });

  it("throws on empty finite domain", () => {
    const gen = new FiniteDomainGenerator<number>();
    const domain = new FiniteDomain<number>([]);
    const rng = rngFromSequence([0.1]);
    expect(() => gen.generate(domain, rng)).toThrow(/empty/i);
  });
});

