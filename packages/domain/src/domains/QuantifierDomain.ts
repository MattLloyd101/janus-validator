import { BaseDomain, Domain } from "../Domain";
import { DomainType } from "../types";

export class QuantifierDomain<T> extends BaseDomain<T[]> {
  readonly kind = DomainType.QUANTIFIER;
  readonly inner: Domain<T>;
  readonly min: number;
  readonly max?: number;

  constructor(inner: Domain<T>, opts: { min: number; max?: number }) {
    super();
    const { min, max } = opts;
    if (min < 0) throw new Error("Quantifier min must be >= 0");
    if (max !== undefined && max < min) throw new Error("Quantifier max must be >= min");
    this.inner = inner;
    this.min = min;
    this.max = max;
  }

  contains(value: unknown): value is T[] {
    if (!Array.isArray(value)) return false;
    if (value.length < this.min) return false;
    if (this.max !== undefined && value.length > this.max) return false;
    return value.every((v) => this.inner.contains(v));
  }

  normalize(): Domain<T[]> {
    return new QuantifierDomain(this.inner.normalize(), { min: this.min, max: this.max });
  }
}

