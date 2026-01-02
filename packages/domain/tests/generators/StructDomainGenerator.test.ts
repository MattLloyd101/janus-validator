import { StructDomain } from "@/domains/StructDomain";
import { FiniteDomain } from "@/domains/FiniteDomain";
import { DomainGeneratorStrategyRegistry } from "@/generators/DomainGeneratorStrategyRegistry";
import { rngFromSequence } from "./helpers";

describe("StructDomainGenerator", () => {
  it("generates object with fields", () => {
    const registry = new DomainGeneratorStrategyRegistry();
    const domain = new StructDomain({
      fields: { a: new FiniteDomain([1]), b: new FiniteDomain(["x", "y"]) },
      strict: true,
    });
    const rng = rngFromSequence([0.2, 0.8]);
    const value = registry.generate(domain, rng);
    expect(value).toEqual({ a: 1, b: "y" });
  });
});

