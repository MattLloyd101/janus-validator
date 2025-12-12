/**
 * Ref domain for references to captured values.
 * Note: Cross-field constraints are intended to be removed per ADR-002.
 */

import { Domain } from './Domain';
import { DomainType, RelationResult, unknown } from './types';

export class RefDomain<T> extends Domain<T> {
  readonly type = DomainType.REF_DOMAIN;

  constructor(public readonly name: string) {
    super();
  }

  protected encapsulatesImpl(_other: Domain<T>): RelationResult {
    // Ref is a cross-field constraint and is intended to be removed per ADR-002.
    // It is not meaningful as a standalone set.
    return unknown('REF_DOMAIN is a cross-field constraint and is not supported for encapsulation');
  }
}
