import { Domain, QuantifierDomain } from '../Domain';
import { RNG } from '../RNG';
import { DomainGeneratorStrategy } from './DomainGeneratorStrategy';
import { DomainGeneratorStrategyRegistry } from './DomainGeneratorStrategyRegistry';

/**
 * Default maximum for unbounded quantifiers when generating
 */
const DEFAULT_MAX_UNBOUNDED = 10;

/**
 * Strategy for generating arrays from a quantifier domain.
 * 
 * Generates an array with a random length between min and max,
 * where each element is generated from the inner domain.
 */
export class QuantifierDomainGenerator<T> implements DomainGeneratorStrategy<T[]> {
  constructor(private registry: DomainGeneratorStrategyRegistry) {}

  /**
   * Generate an array of values from the quantifier domain
   */
  generate(domain: Domain<T[]>, rng: RNG): T[] {
    const quantDomain = domain as QuantifierDomain<T>;
    
    // Cap infinite max for generation
    const effectiveMax = quantDomain.max === Infinity 
      ? DEFAULT_MAX_UNBOUNDED 
      : quantDomain.max;

    // Choose a random count between min and max
    const range = effectiveMax - quantDomain.min + 1;
    const count = quantDomain.min + Math.floor(rng.random() * range);

    // Generate 'count' elements from the inner domain
    const result: T[] = [];
    for (let i = 0; i < count; i++) {
      result.push(this.registry.generate(quantDomain.inner, rng));
    }

    return result;
  }
}
