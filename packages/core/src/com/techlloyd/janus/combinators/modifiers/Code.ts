import { Validator, BaseValidator } from '../../Validator';
import { ValidationResult } from '../../ValidationResult';
import { Domain } from '../../Domain';

/**
 * Wrapper validator that adds an error code.
 * 
 * Error codes are useful for:
 * - i18n: Use codes to look up translated messages
 * - Programmatic handling: Switch on error codes to show different UI
 * - Logging: Categorize errors for analytics
 * 
 * @example
 * ```typescript
 * const email = code(
 *   UnicodeString(5, 100).refine(s => /^[\w.]+@[\w.]+\.\w+$/.test(s)),
 *   'INVALID_EMAIL'
 * );
 * 
 * const result = email.validate('bad');
 * if (!result.valid) {
 *   console.log(result.code); // 'INVALID_EMAIL'
 * }
 * ```
 */
export class CodeValidator<T, D extends Domain<T>> extends BaseValidator<T, D> {
  public readonly domain: D;

  constructor(
    private readonly inner: Validator<T, D>,
    private readonly errorCode: string
  ) {
    super();
    this.domain = inner.domain;
  }

  validate(value: unknown): ValidationResult<T> {
    const result = this.inner.validate(value);
    
    if (result.valid) {
      return result;
    }

    return {
      ...result,
      code: this.errorCode,
    };
  }
}

/**
 * Add an error code to a validator for i18n or programmatic handling.
 * 
 * @param validator The validator to wrap
 * @param errorCode The error code to attach on failure
 * @returns A new validator that includes the error code
 * 
 * @example
 * ```typescript
 * const age = code(Integer(0, 150), 'INVALID_AGE');
 * ```
 */
export function code<T, D extends Domain<T>>(
  validator: Validator<T, D>,
  errorCode: string
): CodeValidator<T, D> {
  return new CodeValidator(validator, errorCode);
}
