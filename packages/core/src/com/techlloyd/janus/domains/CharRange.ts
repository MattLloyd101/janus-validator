/**
 * Character Range utilities for CharSetDomain and regex character classes.
 *
 * CharRange represents a contiguous range of Unicode code points, enabling
 * efficient storage and operations on character sets without enumerating
 * every character.
 */

/**
 * A contiguous range of Unicode code points (inclusive on both ends).
 * Used by CharSetDomain to efficiently represent character classes like [a-z], [0-9A-F], etc.
 */
export interface CharRange {
  readonly min: number; // Unicode code point (inclusive)
  readonly max: number; // Unicode code point (inclusive)
}

/**
 * Normalizes an array of character ranges by sorting and merging overlapping/adjacent ranges.
 * e.g. [{min:0,max:5}, {min:3,max:10}] → [{min:0,max:10}]
 * e.g. [{min:0,max:5}, {min:6,max:10}] → [{min:0,max:10}] (adjacent)
 */
export function normalizeRanges(ranges: readonly CharRange[]): CharRange[] {
  if (ranges.length === 0) return [];

  // Sort by min, then by max descending (so larger ranges come first when mins are equal)
  const sorted = [...ranges].sort((a, b) => a.min - b.min || b.max - a.max);

  const result: CharRange[] = [];
  let current = { ...sorted[0] };

  for (let i = 1; i < sorted.length; i++) {
    const next = sorted[i];
    // Check if next overlaps or is adjacent to current
    if (next.min <= current.max + 1) {
      // Merge: extend current's max if needed
      current.max = Math.max(current.max, next.max);
    } else {
      // No overlap: push current and start new range
      result.push(current);
      current = { ...next };
    }
  }
  result.push(current);

  return result;
}

/**
 * Computes the total number of characters (code points) covered by a set of ranges.
 */
export function rangesSize(ranges: readonly CharRange[]): number {
  return ranges.reduce((sum, r) => sum + (r.max - r.min + 1), 0);
}

/**
 * Checks if all code points in `inner` ranges are covered by `outer` ranges.
 * Returns true if inner ⊆ outer (as sets of code points).
 */
export function rangesSubset(outer: readonly CharRange[], inner: readonly CharRange[]): boolean {
  // For each range in inner, check that it's fully covered by outer ranges
  for (const ir of inner) {
    let pos = ir.min;
    while (pos <= ir.max) {
      // Find an outer range that covers `pos`
      const covering = outer.find((or) => pos >= or.min && pos <= or.max);
      if (!covering) return false;
      // Advance pos to just past this covering range
      pos = covering.max + 1;
    }
  }
  return true;
}

/**
 * Converts a string of characters to normalized CharRange array.
 * e.g. "abc" → [{min: 97, max: 99}]
 * e.g. "aceg" → [{min: 97, max: 97}, {min: 99, max: 99}, {min: 101, max: 101}, {min: 103, max: 103}]
 *   (then normalized to merge adjacent)
 */
export function charsToRanges(chars: string): CharRange[] {
  const codePoints = [...chars].map((c) => c.codePointAt(0)!);
  const ranges: CharRange[] = codePoints.map((cp) => ({ min: cp, max: cp }));
  return normalizeRanges(ranges);
}

/**
 * Creates a single contiguous CharRange from min to max character.
 */
export function charRange(minChar: string, maxChar: string): CharRange {
  return {
    min: minChar.codePointAt(0)!,
    max: maxChar.codePointAt(0)!,
  };
}

