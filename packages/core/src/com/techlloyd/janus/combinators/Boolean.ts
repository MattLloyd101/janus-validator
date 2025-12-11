import { Validator, ValidationResult, FiniteDomain, DomainType } from '../index';

/**
 * Creates a domain for boolean values
 */
function booleanDomain(): FiniteDomain<boolean> {
  return {
    type: DomainType.FINITE_DOMAIN,
    values: [true, false] as const,
  };
}

/**
 * Creates a validator for boolean values
 */
export function Boolean(): Validator<boolean> {
  return {
    validate: (input: unknown): ValidationResult<boolean> => {
      if (typeof input === 'boolean') {
        return { valid: true, value: input };
      }
      return {
        valid: false,
        error: `Expected boolean, got ${typeof input}`,
      };
    },
    domain: booleanDomain(),
  };
}

