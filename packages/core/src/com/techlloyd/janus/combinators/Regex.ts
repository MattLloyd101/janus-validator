import { ValidationResult, RegexDomain, DomainType } from '../index';
import { RegexValidator } from './regex/RegexValidator';
import { parseRegex } from './regex/RegexParser';

/**
 * Creates a validator for strings that match a regular expression pattern.
 * 
 * This function parses the regex pattern into a composed tree of RegexValidator
 * instances, where each node (Literal, CharClass, Sequence, Alternation, etc.)
 * is itself a validator that can match and generate strings.
 * 
 * @param pattern - The RegExp pattern to match against. Can also be a string
 *                  which will be converted to a RegExp.
 * @param flags - Optional flags for the regex (only used when pattern is a string)
 * 
 * @example
 * ```typescript
 * // Match email-like strings
 * const emailValidator = Regex(/^[a-z]+@[a-z]+\.[a-z]+$/);
 * 
 * // Match UUIDs
 * const uuidValidator = Regex(/^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i);
 * 
 * // Using string pattern
 * const digitValidator = Regex('^\\d+$');
 * ```
 */
export function Regex(pattern: RegExp | string, flags?: string): RegexValidator {
  const regex = typeof pattern === 'string' ? new RegExp(pattern, flags) : pattern;
  const source = regex.source;
  
  // Parse the regex pattern into a composed validator tree
  const validator = parseRegex(source);
  
  // Create a wrapper that uses the parsed validator but exposes the original regex
  return new RegexWrapper(validator, regex);
}

/**
 * Wrapper class that combines a parsed RegexValidator with the original RegExp
 */
class RegexWrapper implements RegexValidator {
  private readonly _domain: RegexDomain;

  constructor(
    private readonly validator: RegexValidator,
    private readonly regex: RegExp
  ) {
    this._domain = {
      type: DomainType.REGEX_DOMAIN,
      pattern: regex,
      source: regex.source,
    };
  }

  get domain(): RegexDomain {
    return this._domain;
  }

  validate(value: unknown): ValidationResult<string> {
    if (typeof value !== 'string') {
      return {
        valid: false,
        error: `Expected string, got ${typeof value}`,
      };
    }

    // Use the original regex for validation (handles flags correctly)
    if (!this.regex.test(value)) {
      return {
        valid: false,
        error: `String "${value}" does not match pattern ${this.regex.source}`,
      };
    }

    return { valid: true, value };
  }

  match(input: string, position: number) {
    return this.validator.match(input, position);
  }

  generate(rng: import('../RNG').RNG): string {
    return this.validator.generate(rng);
  }
}

