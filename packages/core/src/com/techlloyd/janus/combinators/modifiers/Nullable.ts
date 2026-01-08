import { Validator, BaseValidator } from '../../Validator';
import { ValidationResult } from '../../ValidationResult';
import { Domain, AlternationDomain, FiniteDomain } from '../../Domain';

/**
 * Wrapper validator that accepts null in addition to the inner type.
 * 
 * This uses composition to wrap any existing validator, allowing it to
 * also accept `null` values.
 * 
 * @example
 * ```typescript
 * const nullableName = new NullableValidator(UnicodeString(1, 50));
 * nullableName.validate("Alice");  // { valid: true, value: "Alice" }
 * nullableName.validate(null);     // { valid: true, value: null }
 * nullableName.validate(undefined); // { valid: false, ... }
 * ```
 */
export class NullableValidator<T, D extends Domain<T>> 
  extends BaseValidator<T | null, AlternationDomain<T | null>> {
  
  public readonly domain: AlternationDomain<T | null>;

  constructor(private readonly inner: Validator<T, D>) {
    super();
    // Domain is an alternation of the inner domain and null
    this.domain = new AlternationDomain<T | null>([
      inner.domain as Domain<T | null>,
      new FiniteDomain([null]) as Domain<T | null>,
    ]);
  }

  validate(value: unknown): ValidationResult<T | null> {
    // Fast path: null is always valid
    if (value === null) {
      return { valid: true, value: null };
    }
    // Otherwise delegate to inner validator
    return this.inner.validate(value) as ValidationResult<T | null>;
  }
}

/**
 * Makes a validator accept null in addition to its normal type.
 * 
 * @param validator The inner validator to wrap
 * @returns A new validator that accepts T | null
 * 
 * @example
 * ```typescript
 * const nullableName = nullable(UnicodeString(1, 50));
 * nullableName.validate("Alice");  // valid
 * nullableName.validate(null);     // valid
 * ```
 */
export function nullable<T, D extends Domain<T>>(
  validator: Validator<T, D>
): Validator<T | null, AlternationDomain<T | null>> {
  return new NullableValidator(validator);
}
