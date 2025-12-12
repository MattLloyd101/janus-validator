/**
 * Capture domain for named capture groups.
 * Note: Cross-field constraints are intended to be removed per ADR-002.
 */

import { Domain } from './Domain';
import { DomainType, RelationResult } from './types';

export class CaptureDomain<T> extends Domain<T> {
  readonly type = DomainType.CAPTURE_DOMAIN;

  constructor(
    public readonly name: string,
    public readonly inner: Domain<T>
  ) {
    super();
  }

  protected encapsulatesImpl(other: Domain<T>): RelationResult {
    // Capture is a cross-field constraint and is intended to be removed per ADR-002.
    // For now, treat it as its inner domain for compatibility reasoning.
    if (other instanceof CaptureDomain) {
      return this.inner.encapsulates(other.inner);
    }
    return this.inner.encapsulates(other);
  }
}
