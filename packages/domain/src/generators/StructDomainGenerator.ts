import { Domain } from "../Domain";
import { StructDomain } from "../domains/StructDomain";
import { DomainGeneratorStrategy } from "./DomainGeneratorStrategy";
import { DomainGeneratorStrategyRegistry } from "./DomainGeneratorStrategyRegistry";
import { RNG } from "./RNG";

export class StructDomainGenerator<T extends Record<string, unknown>> implements DomainGeneratorStrategy<T> {
  constructor(private registry: DomainGeneratorStrategyRegistry) {}

  generate(domain: Domain<T>, rng: RNG): T {
    const struct = domain as StructDomain<any>;
    const result: Record<string, unknown> = {};
    for (const [key, part] of Object.entries(struct.fields)) {
      result[key] = this.registry.generate(part, rng);
    }
    return result as T;
  }
}

