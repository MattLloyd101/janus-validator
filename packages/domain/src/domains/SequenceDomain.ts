import { BaseDomain, Domain } from "../Domain";
import { DomainType } from "../types";

/**
 * Domain representing a fixed-length sequence/tuple of values.
 * Each element is validated against the corresponding part domain.
 */
export class SequenceDomain<T extends readonly unknown[] = readonly unknown[]> extends BaseDomain<T> {
  readonly kind = DomainType.SEQUENCE;
  readonly parts: Domain<any>[];

  constructor(parts: Domain<any>[]) {
    super();
    this.parts = parts;
  }

  contains(value: unknown): value is T {
    if (!Array.isArray(value)) return false;
    if (value.length !== this.parts.length) return false;
    for (let i = 0; i < this.parts.length; i++) {
      if (!this.parts[i].contains(value[i])) return false;
    }
    return true;
  }
}

