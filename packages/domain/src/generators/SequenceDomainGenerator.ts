import { Domain } from "../Domain";
import { SequenceDomain } from "../domains/SequenceDomain";
import { DomainGeneratorStrategy } from "./DomainGeneratorStrategy";
import { DomainGeneratorStrategyRegistry } from "./DomainGeneratorStrategyRegistry";
import { RNG } from "./RNG";

export class SequenceDomainGenerator<T extends readonly unknown[]> implements DomainGeneratorStrategy<T> {
  constructor(private registry: DomainGeneratorStrategyRegistry) {}

  generate(domain: Domain<T>, rng: RNG): T {
    const seq = domain as SequenceDomain<T>;
    const values = seq.parts.map((part) => this.registry.generate(part, rng));
    return values as unknown as T;
  }
}

