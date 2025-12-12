/**
 * Contiguous domain for numeric ranges (min to max inclusive).
 */

import { ContiguousTypeValue } from '../generators/interpolate/ContiguousType';
import { Domain } from './Domain';
import { DomainType, RelationResult, ok, no } from './types';

export class ContiguousDomain extends Domain<number> {
  readonly type = DomainType.CONTIGUOUS_DOMAIN;

  constructor(
    public readonly contiguousType: ContiguousTypeValue,
    public readonly min: number,
    public readonly max: number
  ) {
    super();
  }

  protected encapsulatesImpl(other: Domain<number>): RelationResult {
    if (!(other instanceof ContiguousDomain)) {
      return no(`Domain type mismatch: ${other.type} not subset of ${this.type}`);
    }
    if (this.contiguousType?.name !== other.contiguousType?.name) {
      return no(
        `Contiguous type mismatch: ${other.contiguousType?.name ?? 'unknown'} not subset of ${this.contiguousType?.name ?? 'unknown'}`
      );
    }
    if (this.min > other.min) return no(`Minimum ${other.min} is less than ${this.min}`);
    if (this.max < other.max) return no(`Maximum ${other.max} is greater than ${this.max}`);
    return ok();
  }
}
