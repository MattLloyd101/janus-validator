/**
 * Finite domain: a domain defined by an explicit finite set of values.
 *
 * Universe semantics:
 * - A "root" FiniteDomain has `universe === this` and represents the full universe for its type.
 * - Reductive operations (intersection, difference) return a new FiniteDomain whose `universe`
 *   reference is preserved from the left operand (typically the root universe).
 * - Expansive operations (union) return a new FiniteDomain whose `universe`
 *   is the new result itself (i.e., it expands the universe).
 */

import { AbstractDomain } from './AbstractDomain';
import type { Domain } from './Domain';
import { DomainType } from './DomainType';

function uniqueWithSet<T>(values: readonly T[]): { values: T[]; set: Set<T> } {
  const out: T[] = [];
  const set = new Set<T>();
  for (const v of values ?? []) {
    if (set.has(v)) continue;
    set.add(v);
    out.push(v);
  }
  return { values: out, set };
}

function assertFiniteDomain<T>(other: Domain<T>): asserts other is FiniteDomain<T> {
  if (!(other instanceof FiniteDomain)) {
    throw new Error(`FiniteDomain operation requires FiniteDomain operand`);
  }
}

export class FiniteDomain<T> extends AbstractDomain<T> {
  readonly domainType = DomainType.FINITE_DOMAIN;
  readonly values: readonly T[];
  readonly universe: FiniteDomain<T>;
  private readonly _set: Set<T>;

  /**
   * Create a root finite domain. Root domains are their own universe.
   */
  static of<T>(values: readonly T[]): FiniteDomain<T> {
    return new FiniteDomain<T>(values);
  }

  private constructor(values: readonly T[], universe?: FiniteDomain<T>) {
    super();
    const normalized = uniqueWithSet(values);
    this.values = normalized.values;
    this._set = normalized.set;
    // Root domains are their own universe; derived domains keep a reference to the root universe.
    this.universe = universe ?? this;
  }

  isEmpty(): boolean {
    return this.values.length === 0;
  }

  isDefinedAt(value: T): boolean {
    // Finite domains use SameValueZero equality via Set/Map semantics.
    return this._set.has(value);
  }

  union(other: Domain<T>): FiniteDomain<T> {
    assertFiniteDomain(other);
    // Expansive: new universe is the new product (self-referential).
    return new FiniteDomain<T>([...this.values, ...other.values]);
  }

  intersection(other: Domain<T>): FiniteDomain<T> {
    assertFiniteDomain(other);
    // Reductive: keep left operand's universe reference.
    const kept = (this.values as readonly T[]).filter((v) => other._set.has(v));
    return new FiniteDomain<T>(kept, this.universe);
  }

  difference(other: Domain<T>): FiniteDomain<T> {
    assertFiniteDomain(other);
    // Reductive: keep left operand's universe reference.
    const kept = (this.values as readonly T[]).filter((v) => !other._set.has(v));
    return new FiniteDomain<T>(kept, this.universe);
  }
}


