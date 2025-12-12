import { Domain, SequenceDomain } from '../Domain';
import { RNG } from '../RNG';
import { DomainGeneratorStrategy } from './DomainGeneratorStrategy';
import { DomainGeneratorStrategyRegistry } from './DomainGeneratorStrategyRegistry';

/**
 * Strategy for generating values from a sequence domain.
 * 
 * Generates an array where each element is generated from the corresponding part domain.
 * 
 * ## Type Parameter Trade-off
 * 
 * We use `T extends readonly unknown[]` rather than a more specific constraint because:
 * 
 * 1. TypeScript loses tuple type precision when iterating with `.map()` - even if `parts`
 *    is typed as `[Domain<string>, Domain<number>]`, iterating produces `Domain<string | number>`
 *    per element, and the result widens to `(string | number)[]` instead of `[string, number]`.
 * 
 * 2. The registry receives domains with erased types at runtime, so we can't recover
 *    the exact tuple structure statically.
 * 
 * 3. Recursive conditional types could preserve tuple structure but add significant
 *    complexity and may hit TypeScript depth limits on deeply nested structures.
 * 
 * The `as unknown as T` cast in `generate()` is safe because the runtime behavior
 * correctly produces the tuple - only the static type needs the assertion.
 */
export class SequenceDomainGenerator<T extends readonly unknown[]> implements DomainGeneratorStrategy<T> {
  constructor(private registry: DomainGeneratorStrategyRegistry) {}

  /**
   * Generate an array of values from the sequence domain.
   * Each element is generated from its corresponding part domain.
   */
  generate(domain: Domain<T>, rng: RNG): T {
    const seqDomain = domain as SequenceDomain<T>;
    
    // Cast needed due to TypeScript tuple iteration limitation (see class docs)
    return seqDomain.parts.map(part => this.registry.generate(part, rng)) as unknown as T;
  }
}
