import { Domain, AlternationDomain } from '../Domain';
import { RNG } from '../RNG';
import { DomainGeneratorStrategy } from './DomainGeneratorStrategy';
import { DomainGeneratorStrategyRegistry } from './DomainGeneratorStrategyRegistry';

/**
 * Strategy for generating values from an alternation domain.
 * 
 * Picks one alternative at random and generates a value from its domain.
 * This requires access to the strategy registry to recursively generate
 * from the selected alternative's domain.
 */
export class AlternationDomainGenerator<T> implements DomainGeneratorStrategy<T> {
  constructor(private registry: DomainGeneratorStrategyRegistry) {}

  /**
   * Generate a value by picking a random alternative and generating from it
   */
  generate(domain: Domain<T>, rng: RNG): T {
    const altDomain = domain as AlternationDomain<T>;
    
    if (altDomain.alternatives.length === 0) {
      throw new Error('Cannot generate from alternation with no alternatives');
    }

    // Pick a random alternative
    const index = Math.floor(rng.random() * altDomain.alternatives.length);
    const selectedDomain = altDomain.alternatives[index];

    // Generate from the selected alternative's domain
    return this.registry.generate(selectedDomain, rng);
  }
}
