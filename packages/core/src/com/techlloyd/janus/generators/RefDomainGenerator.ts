import { Domain } from '../Domain';
import { RNG } from '../RNG';
import { DomainGeneratorStrategy } from './DomainGeneratorStrategy';

/**
 * Strategy for generating values from a ref domain.
 * 
 * Since Ref validates that a value matches a captured value,
 * we can't generate independently - we'd need the captured value.
 * For now, we throw an error indicating this limitation.
 */
export class RefDomainGenerator<T> implements DomainGeneratorStrategy<T> {
  generate(_domain: Domain<T>, _rng: RNG): T {
    throw new Error(
      'Cannot generate from RefDomain independently. ' +
      'Use the full validator with Capture to generate valid values.'
    );
  }
}
