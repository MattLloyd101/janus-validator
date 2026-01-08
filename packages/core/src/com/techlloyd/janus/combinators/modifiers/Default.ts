import { Validator, BaseValidator } from '../../Validator';
import { ValidationResult } from '../../ValidationResult';
import { Domain } from '../../Domain';

/**
 * Wrapper validator that provides a default value when input is undefined.
 * 
 * This uses composition to wrap any existing validator. When the input is
 * `undefined`, it returns the default value instead of failing validation.
 * 
 * The default can be a static value or a factory function for dynamic defaults.
 * 
 * @example
 * ```typescript
 * const count = new DefaultValidator(Integer(0, 100), 0);
 * count.validate(42);        // { valid: true, value: 42 }
 * count.validate(undefined); // { valid: true, value: 0 }
 * count.validate(null);      // { valid: false, ... } (null is not undefined)
 * 
 * // Dynamic default
 * const timestamp = new DefaultValidator(Integer(), () => Date.now());
 * timestamp.validate(undefined); // { valid: true, value: <current timestamp> }
 * ```
 */
export class DefaultValidator<T, D extends Domain<T>> extends BaseValidator<T, D> {
  public readonly domain: D;

  constructor(
    private readonly inner: Validator<T, D>,
    private readonly defaultValue: T | (() => T)
  ) {
    super();
    // Domain is unchanged - default just provides a fallback
    this.domain = inner.domain;
  }

  validate(value: unknown): ValidationResult<T> {
    // If undefined, return the default value
    if (value === undefined) {
      const resolved = typeof this.defaultValue === 'function'
        ? (this.defaultValue as () => T)()
        : this.defaultValue;
      return { valid: true, value: resolved };
    }
    // Otherwise delegate to inner validator
    return this.inner.validate(value);
  }
}

/**
 * Provides a default value when input is undefined.
 * 
 * @param validator The inner validator to wrap
 * @param value Default value (static) or factory function (dynamic)
 * @returns A new validator that uses the default for undefined inputs
 * 
 * @example
 * ```typescript
 * // Static default
 * const count = withDefault(Integer(0, 100), 0);
 * count.validate(undefined); // { valid: true, value: 0 }
 * 
 * // Dynamic default (factory function)
 * const timestamp = withDefault(Integer(), () => Date.now());
 * timestamp.validate(undefined); // { valid: true, value: <current timestamp> }
 * ```
 */
export function withDefault<T, D extends Domain<T>>(
  validator: Validator<T, D>,
  value: T | (() => T)
): Validator<T, D> {
  return new DefaultValidator(validator, value);
}
