import { BaseDomain, Domain } from "../Domain";
import { DomainType } from "../types";

export class ContiguousDomain<T extends number | bigint> extends BaseDomain<T> {
  readonly kind = DomainType.CONTIGUOUS;
  readonly min: T;
  readonly max: T;

  constructor(min: T, max: T) {
    super();
    if (min > max) throw new Error("ContiguousDomain min must be <= max");
    this.min = min;
    this.max = max;
  }

  contains(value: unknown): value is T {
    if (typeof this.min === "bigint") {
      if (typeof value !== "bigint") return false;
      return value >= this.min && value <= this.max;
    }
    if (typeof value !== "number" || Number.isNaN(value)) return false;
    return value >= (this.min as number) && value <= (this.max as number);
  }

  normalize(): Domain<T> {
    return new ContiguousDomain(this.min, this.max);
  }
}

