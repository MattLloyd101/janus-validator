import { Domain, FiniteDomain } from '../Domain';
import { RNG } from '../RNG';
import { DomainGeneratorStrategy } from './DomainGeneratorStrategy';

/**
 * Strategy for generating values from a finite domain
 */
export class FiniteDomainGenerator<T> implements DomainGeneratorStrategy<T> {
  generate(domain: Domain<T>, rng: RNG): T {
    const finiteDomain = domain as FiniteDomain<T>;
    const index = Math.floor(rng.random() * finiteDomain.values.length);
    return finiteDomain.values[index];
  }
}

