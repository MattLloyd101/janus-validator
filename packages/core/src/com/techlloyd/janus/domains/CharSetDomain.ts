/**
 * A string domain restricted to a specific charset defined by contiguous code point ranges.
 *
 * This is used by `digits(...)`, `letters(...)`, etc. combinators. Instead of storing
 * all characters explicitly, it stores ranges like `[{min: 0x30, max: 0x39}]` for digits.
 *
 * Benefits:
 * - Efficient storage for large character classes (e.g., all Unicode letters)
 * - Composable: union of ranges via normalization
 * - Enables range-based encapsulation checks
 *
 * @example
 * ```ts
 * // Digits 0-9
 * new CharSetDomain(1, 10, [{ min: 0x30, max: 0x39 }])
 *
 * // Alphanumeric: [0-9A-Za-z]
 * new CharSetDomain(1, 10, [
 *   { min: 0x30, max: 0x39 },  // 0-9
 *   { min: 0x41, max: 0x5A },  // A-Z
 *   { min: 0x61, max: 0x7A },  // a-z
 * ])
 * ```
 */

import { Domain } from './Domain';
import { StringDomain } from './StringDomain';
import { DomainType, RelationResult, ok, no } from './types';
import { CharRange, normalizeRanges, rangesSize, rangesSubset } from './CharRange';

export class CharSetDomain extends Domain<string> {
  readonly type = DomainType.CHARSET_DOMAIN;

  /** Normalized (sorted, merged) ranges of allowed code points */
  readonly ranges: readonly CharRange[];

  /** Total number of distinct characters in the charset */
  readonly size: number;

  constructor(
    public readonly minLength: number,
    public readonly maxLength: number,
    ranges: readonly CharRange[]
  ) {
    super();
    this.ranges = normalizeRanges(ranges);
    this.size = rangesSize(this.ranges);
  }

  protected encapsulatesImpl(other: Domain<string>): RelationResult {
    // Charset domain cannot be a superset of an unrestricted StringDomain.
    if (other instanceof StringDomain) {
      return no(`Domain type mismatch: ${other.type} not subset of ${this.type}`);
    }
    if (!(other instanceof CharSetDomain)) {
      return no(`Domain type mismatch: ${other.type} not subset of ${this.type}`);
    }

    if (this.minLength > other.minLength) return no(`Min length ${other.minLength} is less than ${this.minLength}`);
    if (this.maxLength < other.maxLength) return no(`Max length ${other.maxLength} is greater than ${this.maxLength}`);

    // Check that all characters in other's ranges are covered by this's ranges
    if (!rangesSubset(this.ranges, other.ranges)) {
      return no(`Charset ranges not covered`);
    }

    return ok();
  }
}
