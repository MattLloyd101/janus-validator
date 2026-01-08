import { BaseValidator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { StringDomain } from '../Domain';

/**
 * Validator for Unicode string values with optional length constraints.
 * 
 * @example
 * ```typescript
 * const name = UnicodeString(1, 100);
 * name.validate('Alice');  // valid
 * name.validate('');       // invalid (too short)
 * ```
 */
export class UnicodeStringValidator extends BaseValidator<string> {
  public readonly domain: StringDomain;

  constructor(
    public readonly minLength: number = 0,
    public readonly maxLength: number = Number.MAX_SAFE_INTEGER
  ) {
    super();
    this.domain = new StringDomain({ minLength, maxLength });
  }

  /**
   * Validates that a string contains only valid Unicode scalar values.
   */
  private isValidUnicodeString(str: string): boolean {
    for (let i = 0; i < str.length; i++) {
      const charCode = str.charCodeAt(i);
      
      // High surrogate (0xD800-0xDBFF)
      if (charCode >= 0xD800 && charCode <= 0xDBFF) {
        if (i + 1 >= str.length) {
          return false;
        }
        const nextCharCode = str.charCodeAt(i + 1);
        if (nextCharCode < 0xDC00 || nextCharCode > 0xDFFF) {
          return false;
        }
        i++;
      }
      // Low surrogate without preceding high surrogate
      else if (charCode >= 0xDC00 && charCode <= 0xDFFF) {
        return false;
      }
    }
    return true;
  }

  validate(input: unknown): ValidationResult<string> {
    if (typeof input !== 'string') {
      return this.error(`Expected string, got ${typeof input}`);
    }

    if (!this.isValidUnicodeString(input)) {
      return this.error('Expected valid Unicode string, got string with unpaired surrogates');
    }

    const length = input.length;
    if (length < this.minLength) {
      return this.error(`Expected string length >= ${this.minLength}, got ${length}`);
    }
    if (length > this.maxLength) {
      return this.error(`Expected string length <= ${this.maxLength}, got ${length}`);
    }

    return this.success(input);
  }
}

/**
 * Creates a validator for Unicode string values with optional length constraints.
 */
export function UnicodeString(minLength?: number, maxLength?: number): UnicodeStringValidator {
  return new UnicodeStringValidator(minLength, maxLength);
}
