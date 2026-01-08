import { SequenceDomain } from "@/domains/SequenceDomain";
import { FiniteDomain } from "@/domains/FiniteDomain";
import { DomainGeneratorStrategyRegistry } from "@/generators/DomainGeneratorStrategyRegistry";
import { rngFromSequence } from "./helpers";

describe("SequenceDomainGenerator", () => {
  it("generates tuple values in order", () => {
    const registry = new DomainGeneratorStrategyRegistry();
    const seq = new SequenceDomain<[number, string]>([new FiniteDomain([1]), new FiniteDomain(["x"])]);
    const rng = rngFromSequence([0.1, 0.9]);
    const value = registry.generate(seq, rng);
    expect(value).toEqual([1, "x"]);
  });
});
