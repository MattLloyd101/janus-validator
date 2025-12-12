/**
 * Sequence domain for values that are composed of multiple parts in order.
 * Stores the domains of each part validator.
 */

import { Domain } from './Domain';
import { DomainType, RelationResult, ok, no } from './types';
import type { DomainsForTuple } from '../Types';

/**
 * Domain representing a sequence/tuple of values.
 * Parameterized by the output tuple type T.
 * 
 * @example
 * ```typescript
 * const domain = new SequenceDomain<[string, number]>([stringDomain, numberDomain]);
 * // parts type: [Domain<string>, Domain<number>]
 * // output type: [string, number]
 * ```
 */
export class SequenceDomain<T extends readonly unknown[] = readonly unknown[]> extends Domain<T> {
  readonly type = DomainType.SEQUENCE_DOMAIN;

  constructor(public readonly parts: DomainsForTuple<T>) {
    super();
  }

  protected encapsulatesImpl(other: Domain<T>): RelationResult {
    if (!(other instanceof SequenceDomain)) {
      return no(`Domain type mismatch: ${other.type} not subset of ${this.type}`);
    }
    if ((this.parts?.length ?? 0) !== (other.parts?.length ?? 0)) {
      return no('Sequence length mismatch');
    }
    for (let i = 0; i < (other.parts?.length ?? 0); i++) {
      const res = this.parts[i].encapsulates(other.parts[i]);
      if (res.result !== 'true') return res;
    }
    return ok();
  }
}
