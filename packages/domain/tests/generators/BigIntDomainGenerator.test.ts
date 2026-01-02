import { BigIntDomain } from "@/domains/BigIntDomain";
import { BigIntDomainGenerator } from "@/generators/BigIntDomainGenerator";
import { rngFromSequence } from "./helpers";

describe("BigIntDomainGenerator", () => {
  it("generates bigint within range", () => {
    const gen = new BigIntDomainGenerator();
    const domain = new BigIntDomain(1n, 5n);
    const rng = rngFromSequence([0.5]);
    const value = gen.generate(domain, rng);
    expect(typeof value).toBe("bigint");
    expect((value as bigint) >= 1n && (value as bigint) <= 5n).toBe(true);
  });

  it("handles large ranges by mod sampling", () => {
    const gen = new BigIntDomainGenerator();
    const domain = new BigIntDomain(0n, 10_000_000_000_000_000_000n);
    const rng = rngFromSequence([0.9]);
    const value = gen.generate(domain, rng);
    expect(typeof value).toBe("bigint");
    expect(value >= domain.min && value <= domain.max).toBe(true);
  });

  it("returns min when range is zero", () => {
    const gen = new BigIntDomainGenerator();
    const domain = new BigIntDomain(7n, 7n);
    const rng = rngFromSequence([0.5]);
    expect(gen.generate(domain, rng)).toBe(7n);
  });
});

