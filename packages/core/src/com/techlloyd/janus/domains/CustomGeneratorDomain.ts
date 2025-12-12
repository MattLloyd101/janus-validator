/**
 * Custom generator domain - wraps another domain with custom generation logic.
 * Semantically equivalent to its inner domain for compatibility reasoning.
 */

import type { RNG } from '../RNG';
import { Domain } from './Domain';
import { DomainType, RelationResult } from './types';

export class CustomGeneratorDomain<T> extends Domain<T> {
  readonly type = DomainType.CUSTOM_GENERATOR_DOMAIN;

  constructor(
    public readonly innerDomain: Domain<T>,
    public readonly generate: (rng: RNG) => T
  ) {
    super();
  }

  protected encapsulatesImpl(other: Domain<T>): RelationResult {
    // Semantically, this domain is equivalent to its inner domain.
    return this.innerDomain.encapsulates(other);
  }
}
