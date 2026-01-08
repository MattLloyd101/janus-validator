import { Validator, BaseValidator } from '../../Validator';
import { ValidationResult } from '../../ValidationResult';
import { Domain } from '../../Domain';

/**
 * Wrapper validator that adds a custom predicate check.
 * 
 * The refinement runs after the inner validator succeeds. If the predicate
 * returns false, validation fails with the provided error message.
 * 
 * **Note:** Refinements do NOT affect the domain. Generated values may
 * fail refinement checks. Use refinements for business logic that
 * cannot be expressed as a domain constraint.
 * 
 * @typeParam T - The validated type
 * @typeParam D - The inner domain type
 * 
 * @example
 * ```typescript
 * // Simple predicate
 * const evenNumber = new RefineValidator(
 *   Integer(0, 100),
 *   n => n % 2 === 0,
 *   'Must be even'
 * );
 * 
 * // Dynamic error message
 * const positiveBalance = new RefineValidator(
 *   Float(),
 *   n => n > 0,
 *   n => `Balance must be positive, got ${n}`
 * );
 * ```
 */
export class RefineValidator<T, D extends Domain<T>> extends BaseValidator<T, D> {
  public readonly domain: D;

  constructor(
    private readonly inner: Validator<T, D>,
    private readonly predicate: (value: T) => boolean,
    private readonly message: string | ((value: T) => string)
  ) {
    super();
    // Domain is unchanged - refinements filter, they don't reshape
    this.domain = inner.domain;
  }

  validate(value: unknown): ValidationResult<T> {
    // First run inner validation
    const innerResult = this.inner.validate(value);
    if (!innerResult.valid) {
      return innerResult;
    }

    // Run refinement predicate
    const valid = this.predicate(innerResult.value);
    if (!valid) {
      const errorMsg = typeof this.message === 'function'
        ? this.message(innerResult.value)
        : this.message;
      
      return this.error(errorMsg);
    }

    return innerResult;
  }
}

/**
 * Adds a custom predicate check to a validator.
 * 
 * @param validator The inner validator
 * @param predicate Function that returns true if value is valid
 * @param message Error message or function that generates message
 * @returns A new validator that also checks the predicate
 * 
 * @example
 * ```typescript
 * // Static message
 * const even = refine(I(0, 100), n => n % 2 === 0, 'Must be even');
 * 
 * // Dynamic message
 * const positive = refine(
 *   N(),
 *   n => n > 0,
 *   n => `Expected positive, got ${n}`
 * );
 * ```
 */
export function refine<T, D extends Domain<T>>(
  validator: Validator<T, D>,
  predicate: (value: T) => boolean,
  message: string | ((value: T) => string)
): RefineValidator<T, D> {
  return new RefineValidator(validator, predicate, message);
}
