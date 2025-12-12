import { BaseValidator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { FiniteDomain } from '../Domain';

/**
 * Validator for boolean values.
 */
export class BooleanValidator extends BaseValidator<boolean> {
  public readonly domain: FiniteDomain<boolean> = new FiniteDomain([true, false] as const);

  validate(input: unknown): ValidationResult<boolean> {
    if (typeof input === 'boolean') {
      return this.success(input);
    }
    return this.error(`Expected boolean, got ${typeof input}`);
  }
}

/**
 * Creates a validator for boolean values.
 */
export function Boolean(): BooleanValidator {
  return new BooleanValidator();
}
