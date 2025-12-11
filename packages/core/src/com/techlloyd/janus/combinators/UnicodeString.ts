import { Validator, ValidationResult, StringDomain, DomainType } from '../index';

/**
 * Validates that a string contains only valid Unicode scalar values
 * In JavaScript, strings are UTF-16 internally, but we validate:
 * 1. The string contains only valid Unicode scalar values
 * 2. No unpaired surrogates
 */
function isValidUnicodeString(str: string): boolean {
  // Check for unpaired surrogates
  for (let i = 0; i < str.length; i++) {
    const charCode = str.charCodeAt(i);
    
    // High surrogate (0xD800-0xDBFF)
    if (charCode >= 0xD800 && charCode <= 0xDBFF) {
      // Must be followed by a low surrogate
      if (i + 1 >= str.length) {
        return false; // Unpaired high surrogate
      }
      const nextCharCode = str.charCodeAt(i + 1);
      if (nextCharCode < 0xDC00 || nextCharCode > 0xDFFF) {
        return false; // Not followed by low surrogate
      }
      i++; // Skip the low surrogate
    }
    // Low surrogate (0xDC00-0xDFFF) without preceding high surrogate
    else if (charCode >= 0xDC00 && charCode <= 0xDFFF) {
      return false; // Unpaired low surrogate
    }
  }
  
  return true;
}

/**
 * Creates a domain for string values
 */
function stringDomain(minLength?: number, maxLength?: number): StringDomain {
  return {
    type: DomainType.STRING_DOMAIN,
    minLength,
    maxLength,
  };
}

/**
 * Creates a validator for Unicode string values with optional length constraints.
 * 
 * Validates:
 * - Input is a string type
 * - String contains only valid Unicode scalar values (no unpaired surrogates)
 * - String length is within specified bounds
 * 
 * @param minLength - Minimum string length (optional)
 * @param maxLength - Maximum string length (optional)
 * 
 * @example
 * ```typescript
 * const name = UnicodeString(1, 100);
 * name.validate('Alice');  // ✅ valid
 * name.validate('');       // ❌ too short
 * ```
 */
export function UnicodeString(minLength?: number, maxLength?: number): Validator<string> {
  return {
    validate: (input: unknown): ValidationResult<string> => {
      if (typeof input !== 'string') {
        return {
          valid: false,
          error: `Expected string, got ${typeof input}`,
        };
      }

      // Validate Unicode encoding
      if (!isValidUnicodeString(input)) {
        return {
          valid: false,
          error: 'Invalid string: contains unpaired surrogates',
        };
      }

      // Validate length constraints if provided
      const length = input.length;
      if (minLength !== undefined && length < minLength) {
        return {
          valid: false,
          error: `String length ${length} is less than minimum ${minLength}`,
        };
      }
      if (maxLength !== undefined && length > maxLength) {
        return {
          valid: false,
          error: `String length ${length} is greater than maximum ${maxLength}`,
        };
      }

      return { valid: true, value: input };
    },
    domain: stringDomain(minLength, maxLength),
  };
}


