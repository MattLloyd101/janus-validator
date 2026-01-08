import { Validator, BaseValidator } from '../../Validator';
import { ValidationResult } from '../../ValidationResult';
import { Domain, AlternationDomain, FiniteDomain } from '../../Domain';

/**
 * Wrapper validator that accepts both null and undefined in addition to the inner type.
 * 
 * This uses composition to wrap any existing validator, allowing it to
 * also accept `null` or `undefined` values (nullish values).
 * 
 * @example
 * ```typescript
 * const nullishName = new NullishValidator(UnicodeString(1, 50));
 * nullishName.validate("Alice");    // { valid: true, value: "Alice" }
 * nullishName.validate(null);       // { valid: true, value: null }
 * nullishName.validate(undefined);  // { valid: true, value: undefined }
 * ```
 */
export class NullishValidator<T, D extends Domain<T>> 
  extends BaseValidator<T | null | undefined, AlternationDomain<T | null | undefined>> {
  
  public readonly domain: AlternationDomain<T | null | undefined>;

  constructor(private readonly inner: Validator<T, D>) {
    super();
    // Domain is an alternation of the inner domain, null, and undefined
    this.domain = new AlternationDomain<T | null | undefined>([
      inner.domain as Domain<T | null | undefined>,
      new FiniteDomain([null, undefined]) as Domain<T | null | undefined>,
    ]);
  }

  validate(value: unknown): ValidationResult<T | null | undefined> {
    // Fast path: null and undefined are always valid
    if (value === null) {
      return { valid: true, value: null };
    }
    if (value === undefined) {
      return { valid: true, value: undefined };
    }
    // Otherwise delegate to inner validator
    return this.inner.validate(value) as ValidationResult<T | null | undefined>;
  }
}

/**
 * Makes a validator accept null or undefined in addition to its normal type.
 * 
 * @param validator The inner validator to wrap
 * @returns A new validator that accepts T | null | undefined
 * 
 * @example
 * ```typescript
 * const nullishName = nullish(UnicodeString(1, 50));
 * nullishName.validate("Alice");    // valid
 * nullishName.validate(null);       // valid
 * nullishName.validate(undefined);  // valid
 * ```
 */
export function nullish<T, D extends Domain<T>>(
  validator: Validator<T, D>
): Validator<T | null | undefined, AlternationDomain<T | null | undefined>> {
  return new NullishValidator(validator);
}
