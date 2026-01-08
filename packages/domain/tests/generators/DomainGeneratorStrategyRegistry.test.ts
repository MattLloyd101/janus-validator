import { DomainGeneratorStrategyRegistry } from "@/generators/DomainGeneratorStrategyRegistry";
import { FiniteDomain } from "@/domains/FiniteDomain";
import { DomainType } from "@/types";
import { DomainGeneratorStrategy } from "@/generators/DomainGeneratorStrategy";
import { rngFromSequence } from "./helpers";
import { Domain } from "@/Domain";
import { RNG } from "@/generators/RNG";

class DummyStrategy implements DomainGeneratorStrategy<string> {
  generate(_domain: Domain<string>, _rng: RNG): string {
    return "dummy";
  }
}

describe("DomainGeneratorStrategyRegistry", () => {
  it("generates using registered strategies", () => {
    const registry = new DomainGeneratorStrategyRegistry();
    const rng = rngFromSequence([0.2]);
    const value = registry.generate(new FiniteDomain(["x"]), rng);
    expect(value).toBe("x");
  });

  it("allows overriding strategies", () => {
    const registry = new DomainGeneratorStrategyRegistry();
    registry.register(DomainType.FINITE, new DummyStrategy());
    const rng = rngFromSequence([0.5]);
    const value = registry.generate(new FiniteDomain(["y"]), rng);
    expect(value).toBe("dummy");
  });

  it("throws when strategy missing", () => {
    const registry = new DomainGeneratorStrategyRegistry();
    const fakeType = "unknown_type" as DomainType;
    expect(() => registry.get(fakeType)).toThrow();
  });
});
