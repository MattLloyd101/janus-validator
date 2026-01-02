import { Domain } from "../Domain";
import { AlternationDomain } from "../domains/AlternationDomain";
import { DomainGeneratorStrategy } from "./DomainGeneratorStrategy";
import { DomainGeneratorStrategyRegistry } from "./DomainGeneratorStrategyRegistry";
import { RNG } from "./RNG";

export class AlternationDomainGenerator<T> implements DomainGeneratorStrategy<T> {
  constructor(private registry: DomainGeneratorStrategyRegistry) {}

  generate(domain: Domain<T>, rng: RNG): T {
    const altDomain = domain as AlternationDomain<T>;
    const options = altDomain.options;
    if (options.length === 0) {
      throw new Error("Cannot generate from alternation with no options");
    }
    const index = Math.floor(rng.random() * options.length);
    return this.registry.generate(options[index], rng);
  }
}

