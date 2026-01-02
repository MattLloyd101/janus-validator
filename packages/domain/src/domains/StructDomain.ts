import { BaseDomain, Domain } from "../Domain";
import { DomainType } from "../types";

export class StructDomain<T extends Record<string, unknown>> extends BaseDomain<T> {
  readonly kind = DomainType.STRUCT;
  readonly fields: Record<string, Domain<any>>;
  readonly strict: boolean;

  constructor(opts: { fields: Record<string, Domain<any>>; strict: boolean }) {
    super();
    this.fields = opts.fields;
    this.strict = opts.strict;
  }

  contains(value: unknown): value is T {
    if (typeof value !== "object" || value === null || Array.isArray(value)) return false;
    const keys = Object.keys(this.fields);
    for (const key of keys) {
      if (!(key in (value as any))) return false;
      if (!this.fields[key].contains((value as any)[key])) return false;
    }
    if (this.strict) {
      const extraKeys = Object.keys(value as any).filter((k) => !keys.includes(k));
      if (extraKeys.length > 0) return false;
    }
    return true;
  }
}

