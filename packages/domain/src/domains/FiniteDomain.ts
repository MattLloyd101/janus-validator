import { BaseDomain, Domain } from "../Domain";
import { DomainType } from "../types";

export class FiniteDomain<T> extends BaseDomain<T> {
  readonly kind = DomainType.FINITE;
  protected readonly values: Set<T>;

  constructor(values: Iterable<T>) {
    super();
    this.values = new Set(values);
  }

  get size(): number {
    return this.values.size;
  }

  get all(): T[] {
    return Array.from(this.values);
  }

  contains(value: unknown): value is T {
    return this.values.has(value as T);
  }

  normalize(): Domain<T> {
    return new FiniteDomain(this.values);
  }
}

