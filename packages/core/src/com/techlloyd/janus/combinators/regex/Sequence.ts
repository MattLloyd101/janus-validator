import { RegexDomain, DomainType } from '../../Domain';
import { BaseRegexValidator, MatchResult, RegexValidator } from './RegexValidator';

/**
 * Regex-specific Sequence combinator that matches validators in order.
 * 
 * Unlike the generic Sequence (which validates array elements), this regex
 * Sequence validates that a string matches each validator consecutively,
 * consuming characters as it goes.
 * 
 * This is the regex equivalent of concatenation: abc = RegexSequence(a, b, c)
 * 
 * @example
 * ```typescript
 * const seq = new RegexSequence(new Literal('hello'), new Literal(' '), new Literal('world'));
 * seq.validate('hello world'); // valid
 * seq.validate('helloworld');  // invalid (missing space)
 * ```
 */
export class RegexSequence extends BaseRegexValidator {
  private readonly _domain: RegexDomain;
  public readonly validators: RegexValidator[];

  constructor(...validators: RegexValidator[]) {
    super();
    this.validators = validators;
    
    const source = validators.map(v => (v.domain as RegexDomain).source).join('');
    this._domain = {
      type: DomainType.REGEX_DOMAIN,
      pattern: new RegExp(source),
      source,
    };
  }

  get domain(): RegexDomain {
    return this._domain;
  }

  /**
   * Match all validators in sequence, tracking position
   */
  match(input: string, position: number): MatchResult {
    let currentPos = position;
    let totalConsumed = 0;

    for (const validator of this.validators) {
      const result = validator.match(input, currentPos);
      if (!result.matched) {
        return { matched: false, consumed: 0 };
      }
      currentPos += result.consumed;
      totalConsumed += result.consumed;
    }

    return { matched: true, consumed: totalConsumed };
  }

  /**
   * Factory method to create a regex sequence, flattening nested sequences
   */
  static create(...validators: RegexValidator[]): RegexValidator {
    // Flatten nested sequences
    const flattened: RegexValidator[] = [];
    for (const v of validators) {
      if (v instanceof RegexSequence) {
        flattened.push(...v.validators);
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

    return new RegexSequence(...flattened);
  }
}

// Export alias for backwards compatibility
export { RegexSequence as Sequence };

