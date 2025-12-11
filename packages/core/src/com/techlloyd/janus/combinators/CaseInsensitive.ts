/**
 * CaseInsensitive combinator - makes string validation case-insensitive
 * 
 * Normalizes input to lowercase before validation, preserving the original value on success.
 */

import { Validator, ValidationResult } from '../index';

/**
 * Makes a string validator case-insensitive by normalizing input to lowercase before validation.
 * The original (non-normalized) value is preserved in the result.
 * 
 * @param validator The string validator to make case-insensitive
 * @returns A new validator that accepts both upper and lowercase input
 * 
 * @example
 * ```typescript
 * const hexColor = caseInsensitive(S('#', hex(6)));
 * hexColor.validate('#aabbcc'); // valid
 * hexColor.validate('#AABBCC'); // valid (normalized to lowercase for validation)
 * hexColor.validate('#AaBbCc'); // valid (mixed case)
 * ```
 */
export function caseInsensitive(validator: Validator<string>): Validator<string> {
  return {
    validate: (input: unknown): ValidationResult<string> => {
      if (typeof input !== 'string') {
        return { valid: false, error: `Expected string, got ${typeof input}` };
      }
      
      // Normalize to lowercase for validation
      const normalized = input.toLowerCase();
      const result = validator.validate(normalized);
      
      if (result.valid) {
        // Return original value (preserving case)
        return { valid: true, value: input };
      }
      
      return result;
    },
    domain: validator.domain,
  };
}

