import { BaseValidator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { RegexDomain } from '../Domain';
import { RegexValidator, MatchResult } from './regex/RegexValidator';
import { parseRegex } from './regex/ASTConverter';

/**
 * Creates a validator for strings that match a regular expression pattern.
 * 
 * This function parses the regex pattern into a composed tree of RegexValidator
 * instances, where each node (Literal, CharClass, Sequence, Alternation, etc.)
 * is itself a validator that can match and generate strings.
 * 
 * Note: Only portable regex constructs are supported (see ADR-002).
 * Use explicit character classes instead of escapes:
 * - `[0-9]` instead of `\d`
 * - `[A-Za-z0-9_]` instead of `\w`
 * - `[ \t\r\n]` instead of `\s`
 * 
 * @param pattern - The RegExp pattern to match against. Can also be a string
 *                  which will be converted to a RegExp.
 * @param flags - Regex flags are NOT supported for cross-language portability
 * 
 * @example
 * ```typescript
 * // Match email-like strings
 * const emailValidator = Regex(/^[a-z]+@[a-z]+\.[a-z]+$/);
 * 
 * // Match phone numbers (use [0-9] instead of \d)
 * const phoneValidator = Regex(/^[0-9]{3}-[0-9]{4}$/);
 * 
 * // Match UUIDs
 * const uuidValidator = Regex(/^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/);
 * ```
 */
export function Regex(pattern: RegExp | string, flags?: string): RegexValidator {
  const regex = typeof pattern === 'string' ? new RegExp(pattern, flags) : pattern;
  const source = regex.source;
  
  // Parse the regex pattern into a composed validator tree
  const validator = parseRegex(source, regex.flags);
  
  // Create a wrapper that uses the parsed validator but exposes the original regex
  return new RegexWrapper(validator, regex);
}

/**
 * Wrapper class that combines a parsed RegexValidator with the original RegExp
 */
class RegexWrapper extends BaseValidator<string, RegexDomain> implements RegexValidator {
  public readonly domain: RegexDomain;

  constructor(
    private readonly validator: RegexValidator,
    private readonly regex: RegExp
  ) {
    super();
    this.domain = new RegexDomain(regex);
  }

  validate(value: unknown): ValidationResult<string> {
    if (typeof value !== 'string') {
      return this.error(`Expected string, got ${typeof value}`);
    }

    // Use the original regex for validation (handles flags correctly)
    if (!this.regex.test(value)) {
      return this.error(`Expected string matching /${this.regex.source}/, got "${value}"`);
    }

    return this.success(value);
  }

  match(input: string, position: number): MatchResult {
    return this.validator.match(input, position);
  }
}
