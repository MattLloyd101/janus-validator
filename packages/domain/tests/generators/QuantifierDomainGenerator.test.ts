import { QuantifierDomain } from "@/domains/QuantifierDomain";
import { FiniteDomain } from "@/domains/FiniteDomain";
import { DomainGeneratorStrategyRegistry } from "@/generators/DomainGeneratorStrategyRegistry";
import { rngFromSequence } from "./helpers";

describe("QuantifierDomainGenerator", () => {
  it("generates arrays within bounds", () => {
    const registry = new DomainGeneratorStrategyRegistry();
    const domain = new QuantifierDomain(new FiniteDomain([1]), { min: 2, max: 4 });
    const rng = rngFromSequence([0.0, 0.5, 0.9]);
    const value = registry.generate(domain, rng);
    expect(Array.isArray(value)).toBe(true);
    expect(value.length).toBeGreaterThanOrEqual(2);
    expect(value.length).toBeLessThanOrEqual(4);
    value.forEach((v) => expect(v).toBe(1));
  });

  it("handles undefined max by using min+5 cap", () => {
    const registry = new DomainGeneratorStrategyRegistry();
    const domain = new QuantifierDomain(new FiniteDomain([1]), { min: 1 });
    const rng = rngFromSequence([0.2]);
    const value = registry.generate(domain, rng);
    expect(value.length).toBeGreaterThanOrEqual(1);
    expect(value.length).toBeLessThanOrEqual(6);
  });
});

