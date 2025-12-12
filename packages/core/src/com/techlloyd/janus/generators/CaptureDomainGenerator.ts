import { Domain, CaptureDomain } from '../Domain';
import { RNG } from '../RNG';
import { DomainGeneratorStrategy } from './DomainGeneratorStrategy';
import { DomainGeneratorStrategyRegistry } from './DomainGeneratorStrategyRegistry';

/**
 * Strategy for generating values from a capture domain.
 * Simply delegates to the inner domain's generator.
 */
export class CaptureDomainGenerator<T> implements DomainGeneratorStrategy<T> {
  constructor(private registry: DomainGeneratorStrategyRegistry) {}

  generate(domain: Domain<T>, rng: RNG): T {
    const captureDomain = domain as CaptureDomain<T>;
    return this.registry.generate(captureDomain.inner, rng);
  }
}
