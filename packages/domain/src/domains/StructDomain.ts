import { BaseDomain, Domain } from "../Domain";
import { DomainType } from "../types";

export class StructDomain<T extends Record<string, unknown>> extends BaseDomain<T> {
  readonly kind = DomainType.STRUCT;
  readonly fields: { [K in keyof T]: Domain<T[K]> };
  readonly strict: boolean;

  constructor(opts: { fields: { [K in keyof T]: Domain<T[K]> }; strict: boolean }) {
    super();
    this.fields = opts.fields;
    this.strict = opts.strict;
  }

  contains(value: unknown): value is T {
    if (typeof value !== "object" || value === null || Array.isArray(value)) return false;
    const obj = value as Record<string, unknown>;
    const keys = Object.keys(this.fields) as (keyof T)[];
    for (const key of keys) {
      if (!(key in obj)) return false;
      if (!this.fields[key].contains(obj[key as string])) return false;
    }
    if (this.strict) {
      const extraKeys = Object.keys(obj).filter((k) => !keys.includes(k as keyof T));
      if (extraKeys.length > 0) return false;
    }
    return true;
  }
}

