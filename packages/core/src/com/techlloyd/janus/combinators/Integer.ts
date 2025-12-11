import { Validator, ValidationResult, ContiguousDomain, DomainType, ContiguousType } from '../index';

/**
 * Creates a domain for integer values within a range
 */
function integerDomain(min: number, max: number): ContiguousDomain {
  return {
    type: DomainType.CONTIGUOUS_DOMAIN,
    contiguousType: ContiguousType.INTEGER,
    min,
    max,
  };
}

/**
 * Creates a validator for integer values within an optional range
 * @param min Minimum value (inclusive), defaults to Number.MIN_SAFE_INTEGER
 * @param max Maximum value (inclusive), defaults to Number.MAX_SAFE_INTEGER
 */
export function Integer(
  min: number = Number.MIN_SAFE_INTEGER,
  max: number = Number.MAX_SAFE_INTEGER
): Validator<number> {
  return {
    validate: (input: unknown): ValidationResult<number> => {
      if (typeof input !== 'number') {
        return {
          valid: false,
          error: `Expected number, got ${typeof input}`,
        };
      }

      if (!Number.isFinite(input)) {
        return {
          valid: false,
          error: `Expected finite number, got ${input}`,
        };
      }

      if (!Number.isInteger(input)) {
        return {
          valid: false,
          error: `Expected integer, got ${input}`,
        };
      }

      if (input < min) {
        return {
          valid: false,
          error: `Value ${input} is less than minimum ${min}`,
        };
      }

      if (input > max) {
        return {
          valid: false,
          error: `Value ${input} is greater than maximum ${max}`,
        };
      }

      return { valid: true, value: input };
    },
    domain: integerDomain(min, max),
  };
}

