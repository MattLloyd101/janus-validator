import { Validator, BaseValidator } from '../../Validator';
import { ValidationResult } from '../../ValidationResult';
import { RegexDomain, DomainType } from '../../Domain';

/**
 * Result of a regex match operation
 */
export interface MatchResult {
  matched: boolean;
  consumed: number;
}

/**
 * RegexValidator extends Validator<string> with a match() method for parsing.
 * 
 * This allows regex validators to be composed - each validator can try to match
 * from a position in the string and report how many characters it consumed.
 */
export interface RegexValidator extends Validator<string> {
  /**
   * Try to match this pattern starting at the given position in the input string.
   * Returns the number of characters consumed if matched, or null if no match.
   */
  match(input: string, position: number): MatchResult;
}

/**
 * Base implementation of RegexValidator that provides common functionality
 */
export abstract class BaseRegexValidator extends BaseValidator<string> implements RegexValidator {
  abstract match(input: string, position: number): MatchResult;
  abstract readonly domain: RegexDomain;

  /**
   * Validate that the input is a string that fully matches this pattern
   */
  validate(value: unknown): ValidationResult<string> {
    if (typeof value !== 'string') {
      return this.error(`Expected string, got ${typeof value}`);
    }

    const result = this.match(value, 0);
    if (result.matched && result.consumed === value.length) {
      return this.success(value);
    }

    return this.error(`String "${value}" does not match pattern`);
  }

  /**
   * Create a RegexDomain for this validator
   */
  protected createDomain(): RegexDomain {
    return {
      type: DomainType.REGEX_DOMAIN,
      pattern: new RegExp(''), // Will be overridden by specific validators
      source: '',
    };
  }
}
