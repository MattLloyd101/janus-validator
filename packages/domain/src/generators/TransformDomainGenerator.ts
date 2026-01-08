import { DomainGeneratorStrategy } from "./DomainGeneratorStrategy";
import { TransformDomain } from "../domains/TransformDomain";
import { RNG } from "./RNG";
import { DomainGeneratorStrategyRegistry } from "./DomainGeneratorStrategyRegistry";

/**
 * Generator strategy for TransformDomain.
 * 
 * Generates a value from the inner domain and then applies the transform function.
 * 
 * @example
 * ```typescript
 * const stringDomain = new StringDomain({ minLength: 1, maxLength: 50 });
 * const upperDomain = new TransformDomain(stringDomain, s => s.toUpperCase());
 * 
 * const generator = new TransformDomainGenerator(registry);
 * generator.generate(upperDomain, rng); // "HELLO" (generated "hello", then transformed)
 * ```
 */
export class TransformDomainGenerator<TIn, TOut> 
  implements DomainGeneratorStrategy<TOut> {
  
  constructor(private readonly registry: DomainGeneratorStrategyRegistry) {}

  /**
   * Generates a transformed value.
   * 
   * 1. Generates a value from the inner domain using the registry
   * 2. Applies the transform function to produce the output
   * 
   * @param domain - The TransformDomain to generate from
   * @param rng - Random number generator
   * @returns A transformed value
   */
  generate(domain: TransformDomain<TIn, TOut>, rng: RNG): TOut {
    // Generate from inner domain
    const innerValue = this.registry.generate(domain.inner, rng) as TIn;
    // Apply transform
    return domain.transform(innerValue);
  }
}
