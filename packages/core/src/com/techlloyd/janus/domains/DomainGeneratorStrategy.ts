import { Domain } from '../Domain';
import { RNG } from '../RNG';

/**
 * Strategy interface for generating values from a domain
 */
export interface DomainGeneratorStrategy<T> {
  generate(domain: Domain<T>, rng: RNG): T;
}

