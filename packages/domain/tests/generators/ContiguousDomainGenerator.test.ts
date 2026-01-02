import { ContiguousDomain } from "@/domains/ContiguousDomain";
import { ContiguousDomainGenerator } from "@/generators/ContiguousDomainGenerator";
import { rngFromSequence } from "./helpers";

describe("ContiguousDomainGenerator", () => {
  it("generates within numeric range", () => {
    const gen = new ContiguousDomainGenerator();
    const domain = new ContiguousDomain(0, 10);
    const rng = rngFromSequence([0.5]);
    const value = gen.generate(domain, rng) as number;
    expect(value).toBeGreaterThanOrEqual(0);
    expect(value).toBeLessThanOrEqual(10);
  });

  it("generates float when bounds are fractional", () => {
    const gen = new ContiguousDomainGenerator();
    const domain = new ContiguousDomain(0.5, 1.5);
    const rng = rngFromSequence([0.5]);
    const value = gen.generate(domain, rng) as number;
    expect(value).toBeGreaterThanOrEqual(0.5);
    expect(value).toBeLessThanOrEqual(1.5);
  });

  it("generates bigint within range", () => {
    const gen = new ContiguousDomainGenerator();
    const domain = new ContiguousDomain(1n, 3n);
    const rng = rngFromSequence([0.4]);
    const value = gen.generate(domain, rng);
    expect(typeof value).toBe("bigint");
    expect((value as bigint) >= 1n && (value as bigint) <= 3n).toBe(true);
  });

  it("handles very large bigint ranges", () => {
    const gen = new ContiguousDomainGenerator();
    const domain = new ContiguousDomain(0n, 10_000_000_000_000_000_000n);
    const rng = rngFromSequence([0.8]);
    const value = gen.generate(domain, rng);
    expect(value >= domain.min && value <= domain.max).toBe(true);
  });
});

