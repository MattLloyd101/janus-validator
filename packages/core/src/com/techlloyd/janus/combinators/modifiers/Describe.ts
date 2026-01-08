import { Validator, BaseValidator } from '../../Validator';
import { ValidationResult } from '../../ValidationResult';
import { Domain } from '../../Domain';

/**
 * Wrapper validator that adds a description.
 * 
 * Descriptions are useful for:
 * - Documentation: Auto-generate API docs from schemas
 * - UI hints: Show descriptions as field labels or tooltips
 * - Debugging: Understand what a validator is for
 * 
 * The description is stored on the validator itself and also
 * included in error metadata for context.
 * 
 * @example
 * ```typescript
 * const email = describe(
 *   UnicodeString(5, 100),
 *   'User email address for account recovery'
 * );
 * 
 * console.log(email.description); // 'User email address for account recovery'
 * ```
 */
export class DescribeValidator<T, D extends Domain<T>> extends BaseValidator<T, D> {
  public readonly domain: D;
  public readonly description: string;

  constructor(
    private readonly inner: Validator<T, D>,
    description: string
  ) {
    super();
    this.domain = inner.domain;
    this.description = description;
  }

  validate(value: unknown): ValidationResult<T> {
    const result = this.inner.validate(value);
    
    if (result.valid) {
      return result;
    }

    return {
      ...result,
      meta: {
        ...result.meta,
        description: this.description,
      },
    };
  }
}

/**
 * Add a description to a validator for documentation.
 * 
 * @param validator The validator to wrap
 * @param description Human-readable description of what this field is for
 * @returns A new validator with the description attached
 * 
 * @example
 * ```typescript
 * const username = describe(
 *   UnicodeString(3, 20),
 *   'Unique username for login'
 * );
 * ```
 */
export function describe<T, D extends Domain<T>>(
  validator: Validator<T, D>,
  description: string
): DescribeValidator<T, D> {
  return new DescribeValidator(validator, description);
}
