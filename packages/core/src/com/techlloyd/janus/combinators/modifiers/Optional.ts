import { Validator, BaseValidator } from '../../Validator';
import { ValidationResult } from '../../ValidationResult';
import { Domain, AlternationDomain, FiniteDomain } from '../../Domain';

/**
 * Wrapper validator that accepts undefined in addition to the inner type.
 * 
 * This uses composition to wrap any existing validator, allowing it to
 * also accept `undefined` values.
 * 
 * @example
 * ```typescript
 * const maybeName = new OptionalValidator(UnicodeString(1, 50));
 * maybeName.validate("Alice");    // { valid: true, value: "Alice" }
 * maybeName.validate(undefined);  // { valid: true, value: undefined }
 * maybeName.validate(null);       // { valid: false, ... }
 * ```
 */
export class OptionalValidator<T, D extends Domain<T>> 
  extends BaseValidator<T | undefined, AlternationDomain<T | undefined>> {
  
  public readonly domain: AlternationDomain<T | undefined>;

  constructor(private readonly inner: Validator<T, D>) {
    super();
    // Domain is an alternation of the inner domain and undefined
    this.domain = new AlternationDomain<T | undefined>([
      inner.domain as Domain<T | undefined>,
      new FiniteDomain([undefined]) as Domain<T | undefined>,
    ]);
  }

  validate(value: unknown): ValidationResult<T | undefined> {
    // Fast path: undefined is always valid
    if (value === undefined) {
      return { valid: true, value: undefined };
    }
    // Otherwise delegate to inner validator
    return this.inner.validate(value) as ValidationResult<T | undefined>;
  }
}

/**
 * Makes a validator accept undefined in addition to its normal type.
 * 
 * @param validator The inner validator to wrap
 * @returns A new validator that accepts T | undefined
 * 
 * @example
 * ```typescript
 * const maybeName = optional(UnicodeString(1, 50));
 * maybeName.validate("Alice");    // valid
 * maybeName.validate(undefined);  // valid
 * ```
 */
export function optional<T, D extends Domain<T>>(
  validator: Validator<T, D>
): Validator<T | undefined, AlternationDomain<T | undefined>> {
  return new OptionalValidator(validator);
}
