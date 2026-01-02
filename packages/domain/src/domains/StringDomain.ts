import { BaseDomain, Domain } from "../Domain";
import { DomainType } from "../types";

export class StringDomain extends BaseDomain<string> {
  readonly kind = DomainType.STRING;
  readonly minLength: number;
  readonly maxLength: number;

  constructor(opts: { minLength: number; maxLength: number }) {
    super();
    const { minLength, maxLength } = opts;
    if (minLength < 0 || maxLength < minLength) {
      throw new Error("Invalid string length bounds");
    }
    this.minLength = minLength;
    this.maxLength = maxLength;
  }

  contains(value: unknown): value is string {
    return (
      typeof value === "string" &&
      value.length >= this.minLength &&
      value.length <= this.maxLength
    );
  }
}

