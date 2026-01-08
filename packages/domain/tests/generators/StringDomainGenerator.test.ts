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

  it("caps unbounded maxLength to avoid OOM", () => {
    const gen = new StringDomainGenerator();
    // Simulate UnicodeString() with no bounds - maxLength = Number.MAX_SAFE_INTEGER
    const domain = new StringDomain({ minLength: 0, maxLength: Number.MAX_SAFE_INTEGER });
    // rng.random() = 0.999 would cause ~9 quadrillion char string without the cap
    const rng = rngFromSequence([0.999, ...Array(1000).fill(0.5)]);
    const value = gen.generate(domain, rng);
    // Should be capped at DEFAULT_MAX_GENERATED_LENGTH (1000), not blow up
    expect(value.length).toBeLessThanOrEqual(1000);
  });

  it("respects minLength even when it exceeds the default cap", () => {
    const gen = new StringDomainGenerator();
    // minLength > DEFAULT_MAX_GENERATED_LENGTH should still work
    const domain = new StringDomain({ minLength: 1500, maxLength: 2000 });
    const rng = rngFromSequence([0.0, ...Array(1500).fill(0.5)]);
    const value = gen.generate(domain, rng);
    expect(value.length).toBeGreaterThanOrEqual(1500);
    expect(value.length).toBeLessThanOrEqual(2000);
  });
});

