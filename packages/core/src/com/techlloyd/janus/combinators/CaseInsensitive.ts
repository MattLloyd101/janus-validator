/**
 * CaseInsensitive combinator - makes string validation case-insensitive
 * 
 * Normalizes input to lowercase before validation, preserving the original value on success.
 */

import { Validator, BaseValidator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { Domain } from '../Domain';

/**
 * Validator that makes string validation case-insensitive.
 * Normalizes input to lowercase before validation, preserving the original value on success.
 * 
 * @example
 * ```typescript
 * const hexColor = caseInsensitive(S('#', hex(6)));
 * hexColor.validate('#aabbcc'); // valid
 * hexColor.validate('#AABBCC'); // valid (normalized to lowercase for validation)
 * hexColor.validate('#AaBbCc'); // valid (mixed case)
 * ```
 */
export class CaseInsensitiveValidator extends BaseValidator<string> {
  public readonly domain: Domain<string>;

  constructor(private readonly innerValidator: Validator<string>) {
    super();
    this.domain = innerValidator.domain;
  }

  validate(input: unknown): ValidationResult<string> {
    if (typeof input !== 'string') {
      return this.error(`Expected string, got ${typeof input}`);
    }
    
    // Normalize to lowercase for validation
    const normalized = input.toLowerCase();
    const result = this.innerValidator.validate(normalized);
    
    if (result.valid) {
      // Return original value (preserving case)
      return this.success(input);
    }
    
    return result;
  }
}

/**
 * Makes a string validator case-insensitive by normalizing input to lowercase before validation.
 */
export function caseInsensitive(innerValidator: Validator<string>): CaseInsensitiveValidator {
  return new CaseInsensitiveValidator(innerValidator);
}
