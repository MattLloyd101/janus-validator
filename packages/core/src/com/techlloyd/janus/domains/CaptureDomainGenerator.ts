import { Domain } from '../Domain';
import { RNG } from '../RNG';
import { DomainGeneratorStrategy } from './DomainGeneratorStrategy';
import { DomainGeneratorStrategyRegistry } from './DomainGeneratorStrategyRegistry';

/**
 * Capture domain interface
 */
interface CaptureDomain<T> extends Domain<T> {
  name: string;
  inner: Domain<T>;
}

/**
 * Strategy for generating values from a capture domain.
 * Simply delegates to the inner domain's generator.
 */
export class CaptureDomainGenerator implements DomainGeneratorStrategy<any> {
  constructor(private registry: DomainGeneratorStrategyRegistry) {}

  generate(domain: Domain<any>, rng: RNG): any {
    const captureDomain = domain as CaptureDomain<any>;
    return this.registry.generate(captureDomain.inner, rng);
  }
}

