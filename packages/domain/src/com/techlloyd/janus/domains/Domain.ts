/**
 * Domain interface - represents a set of valid values with set-theoretic operations.
 *
 * Domains are the foundation for validation and generation, defining the space
 * of acceptable values and supporting operations like union, intersection, etc.
 */

import { DomainType } from './DomainType';

export interface Domain<T> {
  /** Identifies the concrete domain kind */
  readonly domainType: DomainType;

  /** The universal domain for this type - represents all possible values */
  readonly universe: Domain<T>;

  /** True iff this domain contains no values. */
  isEmpty(): boolean;

  /** True iff the given value is contained in this domain. */
  isDefinedAt(value: T): boolean;

  /** True iff every value in this domain is also in `other` (this ⊆ other). */
  isSubsetOf(other: Domain<T>): boolean;

  /** True iff every value in `other` is also in this domain (this ⊇ other). */
  isSupersetOf(other: Domain<T>): boolean;

  /** True iff this and other contain exactly the same values (extensional equality). */
  equals(other: Domain<T>): boolean;

  /** Union: values in this OR other */
  union(other: Domain<T>): Domain<T>;

  /** Intersection: values in this AND other */
  intersection(other: Domain<T>): Domain<T>;

  /** Difference: values in this but NOT in other */
  difference(other: Domain<T>): Domain<T>;

  /** Complement: values NOT in this (relative to universe) */
  complement(): Domain<T>;
}


