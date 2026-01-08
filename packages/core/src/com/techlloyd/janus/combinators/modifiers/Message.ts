import { Validator, BaseValidator } from '../../Validator';
import { ValidationResult } from '../../ValidationResult';
import { Domain } from '../../Domain';

/**
 * Wrapper validator that overrides error messages.
 * 
 * This allows customizing the error message shown to users without
 * changing the underlying validation logic.
 * 
 * @example
 * ```typescript
 * // Static message
 * const age = message(Integer(0, 150), 'Please enter a valid age');
 * 
 * // Dynamic message
 * const count = message(Integer(1, 100), (err, val) => 
 *   `Invalid count "${val}": ${err}`
 * );
 * ```
 */
export class MessageValidator<T, D extends Domain<T>> extends BaseValidator<T, D> {
  public readonly domain: D;

  constructor(
    private readonly inner: Validator<T, D>,
    private readonly messageOverride: string | ((error: string, value: unknown) => string)
  ) {
    super();
    this.domain = inner.domain;
  }

  validate(value: unknown): ValidationResult<T> {
    const result = this.inner.validate(value);
    
    if (result.valid) {
      return result;
    }

    const newMessage = typeof this.messageOverride === 'function'
      ? this.messageOverride(result.error, value)
      : this.messageOverride;

    return {
      ...result,
      error: newMessage,
    };
  }
}

/**
 * Override the error message of a validator.
 * 
 * @param validator The validator to wrap
 * @param msg Static message string or function (originalError, value) => message
 * @returns A new validator with the custom message
 * 
 * @example
 * ```typescript
 * const email = message(
 *   UnicodeString(5, 100).refine(s => s.includes('@'), 'Invalid'),
 *   'Please enter a valid email address'
 * );
 * ```
 */
export function message<T, D extends Domain<T>>(
  validator: Validator<T, D>,
  msg: string | ((error: string, value: unknown) => string)
): MessageValidator<T, D> {
  return new MessageValidator(validator, msg);
}
