import { Domain } from './Domain';
import { RNG } from './RNG';
import { DomainGeneratorStrategyRegistry } from './generators/DomainGeneratorStrategyRegistry';

/**
 * Generator class that generates values from a domain using an RNG
 * Uses the strategy pattern to delegate generation to domain-specific strategies
 */
export class Generator {
  private strategyRegistry: DomainGeneratorStrategyRegistry;

  constructor(private rng: RNG, strategyRegistry?: DomainGeneratorStrategyRegistry) {
    this.strategyRegistry = strategyRegistry ?? new DomainGeneratorStrategyRegistry();
  }

  /**
   * Generates a value from the domain using the RNG provided in the constructor
   */
  generate<T>(domain: Domain<T>): T {
    return this.strategyRegistry.generate(domain, this.rng);
  }
}

