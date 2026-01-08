import { BaseDomain, Domain } from "../Domain";
import { DomainType } from "../types";
import type { RNG } from "../generators";

/**
 * Custom generator domain - semantically equivalent to its inner domain,
 * but carries a custom generate function.
 */
export class CustomGeneratorDomain<T, D extends Domain<T>> extends BaseDomain<T> {
  readonly kind = DomainType.CUSTOM_GENERATOR;
  readonly inner: D;
  readonly generate: (rng: RNG) => T;

  constructor(inner: D, generate: (rng: RNG) => T) {
    super();
    this.inner = inner;
    this.generate = generate;
  }

  contains(value: unknown): value is T {
    return this.inner.contains(value);
  }
}

