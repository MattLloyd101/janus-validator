import { BaseValidator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { FiniteDomain, DomainType } from '../Domain';

/**
 * Validator for boolean values.
 */
export class BooleanValidator extends BaseValidator<boolean> {
  public readonly domain: FiniteDomain<boolean> = {
    type: DomainType.FINITE_DOMAIN,
    values: [true, false] as const,
  };

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
