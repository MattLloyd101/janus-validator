import { Domain } from '../Domain';
import { RNG } from '../RNG';
import { DomainGeneratorStrategy } from './DomainGeneratorStrategy';
import { CustomGeneratorDomain } from '../combinators/WithGenerator';

/**
 * Strategy for generating values from a CustomGeneratorDomain.
 * Simply calls the custom generate function provided by the domain.
 */
export class CustomGeneratorDomainGenerator<T> implements DomainGeneratorStrategy<T> {
  generate(domain: Domain<T>, rng: RNG): T {
    const customDomain = domain as CustomGeneratorDomain<T>;
    return customDomain.generate(rng);
  }
}

