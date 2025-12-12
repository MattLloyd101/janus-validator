/**
 * Quantifier domain for repeated values.
 * Validates arrays where each element matches the inner domain.
 */

import { Domain } from './Domain';
import { DomainType, RelationResult, ok, no } from './types';

export class QuantifierDomain<T> extends Domain<T[]> {
  readonly type = DomainType.QUANTIFIER_DOMAIN;

  constructor(
    public readonly inner: Domain<T>,
    public readonly min: number,
    public readonly max: number
  ) {
    super();
  }

  protected encapsulatesImpl(other: Domain<T[]>): RelationResult {
    if (!(other instanceof QuantifierDomain)) {
      return no(`Domain type mismatch: ${other.type} not subset of ${this.type}`);
    }
    if (this.min > other.min) return no(`Min items ${other.min} is less than ${this.min}`);
    if (this.max < other.max) return no(`Max items ${other.max} is greater than ${this.max}`);
    return this.inner.encapsulates(other.inner);
  }
}
