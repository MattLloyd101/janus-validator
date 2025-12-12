/**
 * Bytes domain for binary data (Uint8Array).
 * Supports both variable-length (Bytes) and fixed-length (Fixed) binary.
 */

import { Domain } from './Domain';
import { DomainType, RelationResult, ok, no } from './types';

export class BytesDomain extends Domain<Uint8Array> {
  readonly type = DomainType.BYTES_DOMAIN;

  constructor(
    public readonly minLength: number,
    public readonly maxLength: number
  ) {
    super();
  }

  protected encapsulatesImpl(other: Domain<Buffer>): RelationResult {
    if (!(other instanceof BytesDomain)) {
      return no(`Domain type mismatch: ${other.type} not subset of ${this.type}`);
    }
    if (this.minLength > other.minLength) return no(`Min length ${other.minLength} is less than ${this.minLength}`);
    if (this.maxLength < other.maxLength) return no(`Max length ${other.maxLength} is greater than ${this.maxLength}`);
    return ok();
  }
}
