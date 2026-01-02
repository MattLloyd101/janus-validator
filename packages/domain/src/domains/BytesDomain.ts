import { BaseDomain, Domain } from "../Domain";
import { DomainType } from "../types";

export class BytesDomain extends BaseDomain<Uint8Array> {
  readonly kind = DomainType.BYTES;
  readonly minLength: number;
  readonly maxLength: number;

  constructor(opts: { minLength: number; maxLength: number }) {
    super();
    const { minLength, maxLength } = opts;
    if (minLength < 0 || maxLength < minLength) {
      throw new Error("Invalid byte length bounds");
    }
    this.minLength = minLength;
    this.maxLength = maxLength;
  }

  contains(value: unknown): value is Uint8Array {
    return (
      value instanceof Uint8Array &&
      value.length >= this.minLength &&
      value.length <= this.maxLength
    );
  }

  normalize(): Domain<Uint8Array> {
    return new BytesDomain({ minLength: this.minLength, maxLength: this.maxLength });
  }
}

