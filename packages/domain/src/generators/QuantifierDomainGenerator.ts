import { Domain } from "../Domain";
import { QuantifierDomain } from "../domains/QuantifierDomain";
import { DomainGeneratorStrategy } from "./DomainGeneratorStrategy";
import { DomainGeneratorStrategyRegistry } from "./DomainGeneratorStrategyRegistry";
import { RNG } from "./RNG";

export class QuantifierDomainGenerator<T> implements DomainGeneratorStrategy<T[]> {
  constructor(private registry: DomainGeneratorStrategyRegistry) {}

  generate(domain: Domain<T[]>, rng: RNG): T[] {
    const q = domain as QuantifierDomain<T>;
    const min = q.min;
    const max = q.max ?? min + 5;
    if (max < min) throw new Error("Quantifier max must be >= min");
    const length = min + Math.floor(rng.random() * (max - min + 1));
    const items: T[] = [];
    for (let i = 0; i < length; i++) {
      items.push(this.registry.generate(q.inner, rng));
    }
    return items;
  }
}

