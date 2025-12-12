import { Domain, StructDomain } from '../Domain';
import { RNG } from '../RNG';
import { DomainGeneratorStrategy } from './DomainGeneratorStrategy';
import { DomainGeneratorStrategyRegistry } from './DomainGeneratorStrategyRegistry';

/**
 * Strategy for generating objects from a struct domain.
 * 
 * Generates an object where each property is generated from its corresponding domain.
 */
export class StructDomainGenerator<T extends object> implements DomainGeneratorStrategy<T> {
  constructor(private registry: DomainGeneratorStrategyRegistry) {}

  /**
   * Generate an object from the struct domain
   */
  generate(domain: Domain<T>, rng: RNG): T {
    const structDomain = domain as StructDomain<T>;
    const result: Record<string, unknown> = {};

    for (const key of Object.keys(structDomain.schema) as (keyof T & string)[]) {
      result[key] = this.registry.generate(structDomain.schema[key], rng);
    }

    return result as T;
  }
}
