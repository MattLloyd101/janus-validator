/**
 * Base class for all domains.
 *
 * Domains are used for:
 * - generation (via domain generator strategies)
 * - compatibility reasoning (`encapsulates`)
 *
 * NOTE: Domains may later have a dedicated wire-format serialization; these classes
 * represent the in-process model.
 */

import { DomainType, RelationResult, ok } from './types';

// Forward declarations for type checking (avoids circular import)
interface CustomGeneratorLike<T> {
  type: typeof DomainType.CUSTOM_GENERATOR_DOMAIN;
  innerDomain: Domain<T>;
}

interface AlternationLike<T> {
  type: typeof DomainType.ALTERNATION_DOMAIN;
  alternatives: Domain<T>[];
}

export abstract class Domain<out T> {
  abstract readonly type: DomainType;
  /** @internal - Phantom brand for type inference, not used at runtime */
  readonly __brand?: { readonly _output: T };

  /**
   * Check if this domain encapsulates (is a superset of) another domain.
   * 
   * This method handles common cases:
   * - Unwrapping CustomGeneratorDomain
   * - Checking alternations (all alternatives must be encapsulated)
   * 
   * Subclasses implement `encapsulatesImpl` for type-specific logic.
   */
  encapsulates(other: Domain<T>): RelationResult {
    // Unwrap CustomGeneratorDomain (use type check to avoid circular import)
    let other0: Domain<T> = other;
    while (other0.type === DomainType.CUSTOM_GENERATOR_DOMAIN) {
      other0 = (other0 as unknown as CustomGeneratorLike<T>).innerDomain;
    }

    // Handle alternations: this encapsulates Alternation(...) iff it encapsulates each alternative
    if (other0.type === DomainType.ALTERNATION_DOMAIN) {
      const altDomain = other0 as unknown as AlternationLike<T>;
      for (const alt of altDomain.alternatives) {
        const res = this.encapsulates(alt);
        if (res.result !== 'true') return res;
      }
      return ok();
    }

    // Delegate to type-specific implementation
    return this.encapsulatesImpl(other0);
  }

  /**
   * Type-specific encapsulation logic.
   * Called after unwrapping CustomGeneratorDomain and handling Alternation.
   */
  protected abstract encapsulatesImpl(other: Domain<T>): RelationResult;
}
