/**
 * Abstract base class for Domain implementations.
 *
 * Provides a default implementation of complement() in terms of universe and difference.
 * Concrete subclasses must implement the other set operations.
 */

import { Domain } from './Domain';
import { DomainType } from './DomainType';

export abstract class AbstractDomain<T> implements Domain<T> {
  abstract readonly domainType: DomainType;
  abstract readonly universe: Domain<T>;

  abstract isEmpty(): boolean;
  abstract isDefinedAt(value: T): boolean;

  /**
   * True iff this ⊆ other.
   *
   * Default implementation relies on `difference` + `isEmpty`:
   *   A ⊆ B  iff  (A \\ B) = ∅
   */
  isSubsetOf(other: Domain<T>): boolean {
    return this.difference(other).isEmpty();
  }

  /**
   * True iff this ⊇ other.
   *
   * Default implementation delegates to other's subset check.
   */
  isSupersetOf(other: Domain<T>): boolean {
    return other.isSubsetOf(this);
  }

  /**
   * Extensional equality: A = B iff A ⊆ B and B ⊆ A
   */
  equals(other: Domain<T>): boolean {
    return this.isSubsetOf(other) && other.isSubsetOf(this);
  }

  abstract union(other: Domain<T>): Domain<T>;
  abstract intersection(other: Domain<T>): Domain<T>;
  abstract difference(other: Domain<T>): Domain<T>;

  /**
   * Complement: values NOT in this domain (relative to universe).
   * Default implementation: universe.difference(this)
   */
  complement(): Domain<T> {
    return this.universe.difference(this);
  }
}


