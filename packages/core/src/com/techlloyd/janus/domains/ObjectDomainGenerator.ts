import { Domain } from '../Domain';
import { RNG } from '../RNG';
import { DomainGeneratorStrategy } from './DomainGeneratorStrategy';
import { DomainGeneratorStrategyRegistry } from './DomainGeneratorStrategyRegistry';

/**
 * Struct domain interface (matches the one in Struct.ts)
 */
interface StructDomain extends Domain<object> {
  schema: { [key: string]: Domain<any> };
  strict: boolean;
}

/**
 * Strategy for generating objects from a struct domain.
 * 
 * Generates an object where each property is generated from its corresponding domain.
 */
export class StructDomainGenerator implements DomainGeneratorStrategy<object> {
  constructor(private registry: DomainGeneratorStrategyRegistry) {}

  /**
   * Generate an object from the struct domain
   */
  generate(domain: Domain<object>, rng: RNG): object {
    const structDomain = domain as StructDomain;
    const result: Record<string, any> = {};

    for (const [key, propDomain] of Object.entries(structDomain.schema)) {
      result[key] = this.registry.generate(propDomain, rng);
    }

    return result;
  }
}

