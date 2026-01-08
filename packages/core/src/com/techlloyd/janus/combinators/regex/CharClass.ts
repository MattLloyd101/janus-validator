import { CharRange } from '@janus-validator/regex-parser';
import { RegexDomain } from '../../Domain';
import { BaseRegexValidator, MatchResult } from './RegexValidator';

/**
 * Build a CharRange (inclusive) from two characters.
 */
function charRange(start: string, end: string): CharRange {
  const min = start.codePointAt(0);
  const max = end.codePointAt(0);
  if (min === undefined || max === undefined) {
    throw new Error('charRange requires non-empty strings');
  }
  if (min > max) {
    throw new Error('charRange start must be <= end');
  }
  return { min, max };
}

/**
 * Validator that matches one character from a set of character ranges.
 * 
 * Uses contiguous code point ranges for efficient containment checks,
 * avoiding the need to enumerate all characters in the class.
 * 
 * Note: Negated character classes [^...] are not supported.
 * 
 * @example
 * ```ts
 * // Match digits [0-9]
 * new CharClass([{ min: 0x30, max: 0x39 }])
 * 
 * // Match word characters [a-zA-Z0-9_]
 * new CharClass([
 *   { min: 0x30, max: 0x39 },  // 0-9
 *   { min: 0x41, max: 0x5A },  // A-Z
 *   { min: 0x5F, max: 0x5F },  // _
 *   { min: 0x61, max: 0x7A },  // a-z
 * ])
 * ```
 */
export class CharClass extends BaseRegexValidator {
  private readonly _domain: RegexDomain;

  constructor(
    public readonly ranges: readonly CharRange[],
    negated: boolean = false
  ) {
    super();
    if (negated) {
      throw new Error("Unsupported regex construct: negated character class");
    }
    const source = this.buildSource();
    this._domain = new RegexDomain(new RegExp(source));
  }

  get domain(): RegexDomain {
    return this._domain;
  }

  match(input: string, position: number): MatchResult {
    if (position >= input.length) {
      return { matched: false, consumed: 0 };
    }

    const codePoint = input.codePointAt(position)!;
    const matched = this.containsCodePoint(codePoint);

    return { matched, consumed: matched ? 1 : 0 };
  }

  /**
   * Check if a code point falls within any of the ranges.
   */
  private containsCodePoint(codePoint: number): boolean {
    for (const range of this.ranges) {
      if (codePoint >= range.min && codePoint <= range.max) {
        return true;
      }
    }
    return false;
  }

  private buildSource(): string {
    const parts = this.ranges.map(r => {
      const minChar = String.fromCodePoint(r.min);
      const maxChar = String.fromCodePoint(r.max);
      if (r.min === r.max) {
        return this.escapeForCharClass(minChar);
      }
      return `${this.escapeForCharClass(minChar)}-${this.escapeForCharClass(maxChar)}`;
    });
    const inner = parts.join('');
    return `[${inner}]`;
  }

  private escapeForCharClass(char: string): string {
    if (char === ']' || char === '\\' || char === '^' || char === '-') {
      return '\\' + char;
    }
    return char;
  }
}

// ============================================================================
// Predefined character class ranges
// ============================================================================

/** Range for digits 0-9 */
const DIGIT_RANGE: CharRange = charRange('0', '9');

/** Ranges for word characters [a-zA-Z0-9_] */
const WORD_RANGES: readonly CharRange[] = [
  charRange('0', '9'),
  charRange('A', 'Z'),
  { min: 0x5F, max: 0x5F }, // underscore
  charRange('a', 'z'),
];

/** Ranges for whitespace characters (space, tab, newline, carriage return, form feed, vertical tab) */
const WHITESPACE_RANGES: readonly CharRange[] = [
  { min: 0x09, max: 0x0D }, // \t \n \v \f \r (contiguous in ASCII)
  { min: 0x20, max: 0x20 }, // space
];

/**
 * Common character class factories
 */
export const CharClasses = {
  /** Matches any digit [0-9] */
  digit(): CharClass {
    return new CharClass([DIGIT_RANGE]);
  },

  /** Matches any word character [a-zA-Z0-9_] */
  word(): CharClass {
    return new CharClass(WORD_RANGES);
  },

  /** Matches any whitespace character [ \t\n\r\f\v] */
  whitespace(): CharClass {
    return new CharClass(WHITESPACE_RANGES);
  },

  /** Creates a character range, e.g., 'a' to 'z' */
  range(start: string, end: string): CharClass {
    return new CharClass([charRange(start, end)]);
  },

  /** Creates a CharClass from explicit ranges */
  fromRanges(ranges: readonly CharRange[]): CharClass {
    return new CharClass(ranges);
  },
};

export { charRange };
export type { CharRange };

