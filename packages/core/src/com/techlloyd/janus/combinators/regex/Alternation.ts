import { RegexDomain, DomainType } from '../../Domain';
import { RNG } from '../../RNG';
import { MatchResult, RegexValidator } from './RegexValidator';
import { Alternation as GenericAlternation } from '../Alternation';
import { ValidationResult } from '../../ValidationResult';

/**
 * Regex-specific Alternation combinator that extends the generic Alternation<string>
 * with regex-specific behavior:
 * - `match()` method for parsing strings character by character
 * - `generate()` method for producing matching strings
 * - Constructs a RegexDomain with the combined source pattern
 * 
 * @example
 * ```typescript
 * // This is the regex equivalent of: a|b|c
 * const alt = new RegexAlternation(new Literal('a'), new Literal('b'), new Literal('c'));
 * ```
 */
export class RegexAlternation extends GenericAlternation<string, RegexDomain> implements RegexValidator {
  private readonly regexValidators: RegexValidator[];

  constructor(...validators: RegexValidator[]) {
    super(...validators);
    this.regexValidators = validators;
    
    const source = validators.map(v => {
      // Wrap in non-capturing group if needed to preserve precedence
      const s = (v.domain as RegexDomain).source;
      return s.includes('|') ? `(?:${s})` : s;
    }).join('|');
    
    // Override the domain with RegexDomain
    (this as any)._domain = {
      type: DomainType.REGEX_DOMAIN,
      pattern: new RegExp(source),
      source,
    };
  }

  /**
   * Override validate to provide better error messages for regex context
   */
  validate(value: unknown): ValidationResult<string> {
    if (typeof value !== 'string') {
      return {
        valid: false,
        error: `Expected string, got ${typeof value}`,
      };
    }

    const result = this.match(value, 0);
    if (result.matched && result.consumed === value.length) {
      return { valid: true, value };
    }

    return {
      valid: false,
      error: `String "${value}" does not match pattern`,
    };
  }

  /**
   * Try to match at the given position, returning first matching alternative
   */
  match(input: string, position: number): MatchResult {
    for (const validator of this.regexValidators) {
      const result = validator.match(input, position);
      if (result.matched) {
        return result;
      }
    }
    return { matched: false, consumed: 0 };
  }

  /**
   * Generate a string by randomly selecting one alternative
   */
  generate(rng: RNG): string {
    if (this.regexValidators.length === 0) {
      return '';
    }
    const index = Math.floor(rng.random() * this.regexValidators.length);
    return this.regexValidators[index].generate(rng);
  }

  /**
   * Factory method to create a regex alternation, flattening nested alternations
   */
  static create(...validators: RegexValidator[]): RegexValidator {
    // Flatten nested alternations
    const flattened: RegexValidator[] = [];
    for (const v of validators) {
      if (v instanceof RegexAlternation) {
        flattened.push(...v.regexValidators);
      } else {
        flattened.push(v);
      }
    }

    // Handle edge cases
    if (flattened.length === 0) {
      const { Empty } = require('./Empty');
      return new Empty();
    }
    if (flattened.length === 1) {
      return flattened[0];
    }

    return new RegexAlternation(...flattened);
  }
}

// Export alias for backwards compatibility
export { RegexAlternation as Alternation };

