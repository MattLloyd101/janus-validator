import { BytesDomain } from "@/domains/BytesDomain";
import { BytesDomainGenerator } from "@/generators/BytesDomainGenerator";
import { rngFromSequence } from "./helpers";

describe("BytesDomainGenerator", () => {
  it("generates Uint8Array within length bounds", () => {
    const gen = new BytesDomainGenerator();
    const domain = new BytesDomain({ minLength: 1, maxLength: 3 });
    const rng = rngFromSequence([0.1, 0.5, 0.9]);
    const value = gen.generate(domain, rng);
    expect(value instanceof Uint8Array).toBe(true);
    expect(value.length).toBeGreaterThanOrEqual(1);
    expect(value.length).toBeLessThanOrEqual(3);
  });
});

