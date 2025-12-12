/**
 * Alternation domain for values that can match one of several alternatives.
 * Stores the domains of each alternative validator.
 */

import { Domain } from './Domain';
import { DomainType, RelationResult, ok, unknown } from './types';

export class AlternationDomain<T> extends Domain<T> {
  readonly type = DomainType.ALTERNATION_DOMAIN;

  constructor(public readonly alternatives: Domain<T>[]) {
    super();
  }

  /**
   * AlternationDomain has special encapsulation logic:
   * - this encapsulates other iff ANY branch encapsulates other
   * 
   * Note: The base class handles the case where `other` is an alternation
   * (checking each alternative), so encapsulatesImpl only needs to handle
   * when `other` is a non-alternation.
   */
  protected encapsulatesImpl(other: Domain<T>): RelationResult {
    // Flatten nested alternations
    const branches = this.flattenAlternatives();

    // `this` (a union) encapsulates `other` if ANY branch encapsulates it.
    const reasons: string[] = [];
    for (const branch of branches) {
      const res = branch.encapsulates(other);
      if (res.result === 'true') return ok();
      if (res.result === 'false') reasons.push(res.reason);
    }
    return unknown(
      reasons.length
        ? `No alternation branch encapsulates source; reasons: ${reasons.join('; ')}`
        : 'No alternation branch encapsulates source'
    );
  }

  /**
   * Flatten nested alternations into a single array of non-alternation domains.
   * Note: CustomGeneratorDomain unwrapping is handled by encapsulates() calls.
   */
  private flattenAlternatives(): Domain<T>[] {
    const result: Domain<T>[] = [];
    for (const alt of this.alternatives ?? []) {
      if (alt instanceof AlternationDomain) {
        result.push(...alt.flattenAlternatives());
      } else {
        result.push(alt);
      }
    }
    return result;
  }
}
