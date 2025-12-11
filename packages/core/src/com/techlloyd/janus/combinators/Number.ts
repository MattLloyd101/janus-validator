import { Validator, ValidationResult, ContiguousDomain, DomainType, ContiguousType } from '../index';

/**
 * Creates a domain for floating-point number values within a range
 */
function numberDomain(min: number, max: number): ContiguousDomain {
  return {
    type: DomainType.CONTIGUOUS_DOMAIN,
    contiguousType: ContiguousType.FLOAT,
    min,
    max,
  };
}

/**
 * Creates a validator for floating-point number values within an optional range
 * @param min Minimum value (inclusive), defaults to -Number.MAX_VALUE
 * @param max Maximum value (inclusive), defaults to Number.MAX_VALUE
 * 
 * @example
 * ```typescript
 * const percent = Number(0, 100);
 * percent.validate(50.5);   // valid
 * percent.validate(0);      // valid
 * percent.validate(-1);     // invalid (below min)
 * percent.validate(100.1);  // invalid (above max)
 * 
 * const anyNumber = Number();
 * anyNumber.validate(3.14159);  // valid
 * anyNumber.validate(-1e10);    // valid
 * ```
 */
export function Number(
  min: number = -globalThis.Number.MAX_VALUE,
  max: number = globalThis.Number.MAX_VALUE
): Validator<number> {
  return {
    validate: (input: unknown): ValidationResult<number> => {
      if (typeof input !== 'number') {
        return {
          valid: false,
          error: `Expected number, got ${typeof input}`,
        };
      }

      if (!globalThis.Number.isFinite(input)) {
        return {
          valid: false,
          error: `Expected finite number, got ${input}`,
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
    domain: numberDomain(min, max),
  };
}

