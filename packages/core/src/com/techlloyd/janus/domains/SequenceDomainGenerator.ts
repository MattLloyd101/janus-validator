import { Domain, SequenceDomain } from '../Domain';
import { RNG } from '../RNG';
import { DomainGeneratorStrategy } from './DomainGeneratorStrategy';
import { DomainGeneratorStrategyRegistry } from './DomainGeneratorStrategyRegistry';

/**
 * Strategy for generating values from a sequence domain.
 * 
 * Generates an array where each element is generated from the corresponding part domain.
 */
export class SequenceDomainGenerator implements DomainGeneratorStrategy<any[]> {
  constructor(private registry: DomainGeneratorStrategyRegistry) {}

  /**
   * Generate an array of values from the sequence domain
   * Each element is generated from its corresponding part domain.
   */
  generate(domain: Domain<any[]>, rng: RNG): any[] {
    const seqDomain = domain as SequenceDomain<any>;
    
    return seqDomain.parts.map(part => this.registry.generate(part, rng));
  }
}

