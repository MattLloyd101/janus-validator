import { RegexDomain } from '../../Domain';
import { BaseRegexValidator, MatchResult, RegexValidator } from './RegexValidator';

/**
 * Regex-specific Quantifier that matches a validator repeated a number of times.
 * 
 * Unlike the generic Quantifier (which validates arrays), this regex Quantifier
 * validates that a string matches the inner pattern repeated between min and max times.
 * 
 * Supports regex quantifier syntax:
 * - * (zero or more): RegexQuantifier(v, 0, Infinity)
 * - + (one or more): RegexQuantifier(v, 1, Infinity)
 * - ? (zero or one): RegexQuantifier(v, 0, 1)
 * - {n} (exactly n): RegexQuantifier(v, n, n)
 * - {n,} (n or more): RegexQuantifier(v, n, Infinity)
 * - {n,m} (between n and m): RegexQuantifier(v, n, m)
 * 
 * @example
 * ```typescript
 * const digits = new RegexQuantifier(CharClasses.digit(), 3, 3);
 * digits.validate('123');  // valid
 * digits.validate('12');   // invalid (too few)
 * digits.validate('1234'); // invalid (too many)
 * ```
 */
export class RegexQuantifier extends BaseRegexValidator {
  private readonly _domain: RegexDomain;

  constructor(
    public readonly validator: RegexValidator,
    public readonly min: number,
    public readonly max: number
  ) {
    super();
    
    const source = this.buildSource();
    this._domain = new RegexDomain(new RegExp(source));
  }

  get domain(): RegexDomain {
    return this._domain;
  }

  match(input: string, position: number): MatchResult {
    let currentPos = position;
    let count = 0;

    // Greedy matching: try to match as many as possible up to max
    const effectiveMax = this.max === Infinity ? input.length : this.max;

    while (count < effectiveMax) {
      const result = this.validator.match(input, currentPos);
      if (!result.matched) {
        break;
      }
      // Prevent infinite loop on zero-width matches
      if (result.consumed === 0 && count >= this.min) {
        break;
      }
      currentPos += result.consumed;
      count++;
    }

    if (count >= this.min) {
      return { matched: true, consumed: currentPos - position };
    }

    return { matched: false, consumed: 0 };
  }

  private buildSource(): string {
    const inner = this.wrapIfNeeded(this.getValidatorSource());

    if (this.min === 0 && this.max === Infinity) {
      return `${inner}*`;
    }
    if (this.min === 1 && this.max === Infinity) {
      return `${inner}+`;
    }
    if (this.min === 0 && this.max === 1) {
      return `${inner}?`;
    }
    if (this.min === this.max) {
      return `${inner}{${this.min}}`;
    }
    if (this.max === Infinity) {
      return `${inner}{${this.min},}`;
    }
    return `${inner}{${this.min},${this.max}}`;
  }

  private wrapIfNeeded(source: string): string {
    // Wrap in non-capturing group if the source is more than one character
    // and doesn't already have grouping
    if (source.length > 1 && !source.startsWith('(') && !source.startsWith('[')) {
      return `(?:${source})`;
    }
    return source;
  }

  private getValidatorSource(): string {
    return (this.validator.domain as RegexDomain).source;
  }

  /**
   * Factory methods for common quantifiers
   */
  static zeroOrMore(validator: RegexValidator): RegexQuantifier {
    return new RegexQuantifier(validator, 0, Infinity);
  }

  static oneOrMore(validator: RegexValidator): RegexQuantifier {
    return new RegexQuantifier(validator, 1, Infinity);
  }

  static optional(validator: RegexValidator): RegexQuantifier {
    return new RegexQuantifier(validator, 0, 1);
  }

  static exactly(validator: RegexValidator, n: number): RegexQuantifier {
    return new RegexQuantifier(validator, n, n);
  }

  static atLeast(validator: RegexValidator, n: number): RegexQuantifier {
    return new RegexQuantifier(validator, n, Infinity);
  }

  static between(validator: RegexValidator, min: number, max: number): RegexQuantifier {
    return new RegexQuantifier(validator, min, max);
  }
}

// Export alias for backwards compatibility
export { RegexQuantifier as Quantifier };

