/**
 * BigInt domain for 64-bit integer values (and beyond).
 * Uses JavaScript's BigInt for arbitrary precision integers.
 */

import { Domain } from './Domain';
import { DomainType, RelationResult, ok, no } from './types';

export class BigIntDomain extends Domain<bigint> {
  readonly type = DomainType.BIGINT_DOMAIN;

  constructor(
    public readonly min: bigint,
    public readonly max: bigint
  ) {
    super();
  }

  protected encapsulatesImpl(other: Domain<bigint>): RelationResult {
    if (!(other instanceof BigIntDomain)) {
      return no(`Domain type mismatch: ${other.type} not subset of ${this.type}`);
    }
    if (this.min > other.min) return no(`Minimum ${other.min.toString()} is less than ${this.min.toString()}`);
    if (this.max < other.max) return no(`Maximum ${other.max.toString()} is greater than ${this.max.toString()}`);
    return ok();
  }
}
