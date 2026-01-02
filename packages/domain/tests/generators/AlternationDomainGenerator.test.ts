import { AlternationDomain } from "@/domains/AlternationDomain";
import { FiniteDomain } from "@/domains/FiniteDomain";
import { AlternationDomainGenerator } from "@/generators/AlternationDomainGenerator";
import { DomainGeneratorStrategyRegistry } from "@/generators/DomainGeneratorStrategyRegistry";
import { rngFromSequence } from "./helpers";

describe("AlternationDomainGenerator", () => {
  it("generates from one of the alternatives", () => {
    const registry = new DomainGeneratorStrategyRegistry();
    const gen = new AlternationDomainGenerator<string>(registry);
    const alt = new AlternationDomain([new FiniteDomain(["a"]), new FiniteDomain(["b"])]);
    const rng = rngFromSequence([0.1]);
    const value = gen.generate(alt, rng);
    expect(["a", "b"]).toContain(value);
  });

  it("throws when no options", () => {
    const registry = new DomainGeneratorStrategyRegistry();
    const gen = new AlternationDomainGenerator<string>(registry);
    const alt = new AlternationDomain<string>([]);
    const rng = rngFromSequence([0.5]);
    expect(() => gen.generate(alt, rng)).toThrow();
  });
});

