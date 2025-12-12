/**
 * String domain for valid Unicode strings.
 */

import { Domain } from './Domain';
import { DomainType, RelationResult, ok, no, unknown } from './types';

export class StringDomain extends Domain<string> {
  readonly type = DomainType.STRING_DOMAIN;
  /** Optional internal compound-parts model used by generators/compat checks */
  readonly _parts?: Array<string | Domain<string>>;

  constructor(
    public readonly minLength?: number,
    public readonly maxLength?: number,
    extras?: Partial<Pick<StringDomain, '_parts'>>
  ) {
    super();
    if (extras) Object.assign(this, extras);
  }

  protected encapsulatesImpl(other: Domain<string>): RelationResult {
    if (!(other instanceof StringDomain)) {
      return no(`Domain type mismatch: ${other.type} not subset of ${this.type}`);
    }

    const aMin = other.minLength ?? 0;
    const aMax = other.maxLength ?? Number.POSITIVE_INFINITY;
    const bMin = this.minLength ?? 0;
    const bMax = this.maxLength ?? Number.POSITIVE_INFINITY;

    if (bMin > aMin) return no(`Min length ${aMin} is less than ${bMin}`);
    if (bMax < aMax) return no(`Max length ${aMax} is greater than ${bMax}`);

    const aParts = other._parts;
    const bParts = this._parts;
    if (aParts || bParts) {
      if (!aParts || !bParts) {
        return unknown('Compound string parts comparison requires both domains to have _parts');
      }
      if (aParts.length !== bParts.length) {
        return unknown('Compound string parts comparison requires equal part lengths (string-language model not implemented yet)');
      }
      for (let i = 0; i < aParts.length; i++) {
        const ap = aParts[i];
        const bp = bParts[i];
        if (typeof ap === 'string' && typeof bp === 'string') {
          if (ap !== bp) return no(`Literal part mismatch at index ${i}`);
        } else if (typeof ap === 'string' || typeof bp === 'string') {
          return unknown(`Mixed literal/domain part comparison at index ${i} requires string-language model`);
        } else {
          const res = bp.encapsulates(ap);
          if (res.result !== 'true') return res;
        }
      }
    }

    return ok();
  }
}
