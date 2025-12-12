import { Domain, ContiguousDomain } from '../Domain';
import { RNG } from '../RNG';
import { DomainGeneratorStrategy } from './DomainGeneratorStrategy';

/**
 * Strategy for generating values from a contiguous domain (numeric range)
 * Uses the interpolation strategy directly from the ContiguousType
 */
export class ContiguousDomainGenerator implements DomainGeneratorStrategy<number> {
  generate(domain: Domain<number>, rng: RNG): number {
    const contiguousDomain = domain as ContiguousDomain;
    const { min, max, contiguousType } = contiguousDomain;
    
    return contiguousType.strategy.interpolate(min, max, rng);
  }
}

