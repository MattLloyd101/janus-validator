/**
 * Finite domain for values with a fixed set of possible values.
 */

import { Domain } from './Domain';
import { DomainType, RelationResult, ok, no } from './types';

export class FiniteDomain<T> extends Domain<T> {
  readonly type = DomainType.FINITE_DOMAIN;

  constructor(public readonly values: readonly T[]) {
    super();
  }

  protected encapsulatesImpl(other: Domain<T>): RelationResult {
    if (!(other instanceof FiniteDomain)) {
      return no(`Domain type mismatch: ${other.type} not subset of ${this.type}`);
    }
    const set = new Set(this.values as readonly any[]);
    for (const v of other.values ?? []) {
      if (!set.has(v)) return no(`Missing finite value: ${String(v)}`);
    }
    return ok();
  }
}
