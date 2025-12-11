import { Validator, ValidationResult, BigIntDomain, DomainType } from '../index';

/**
 * Default min value for Long: Avro long min (-2^63)
 */
const LONG_MIN = -(2n ** 63n);

/**
 * Default max value for Long: Avro long max (2^63 - 1)
 */
const LONG_MAX = 2n ** 63n - 1n;

/**
 * Creates a domain for BigInt values
 */
function bigIntDomain(min: bigint, max: bigint): BigIntDomain {
  return {
    type: DomainType.BIGINT_DOMAIN,
    min,
    max,
  };
}

/**
 * Converts various input types to BigInt if possible
 */
function toBigInt(input: unknown): bigint | null {
  if (typeof input === 'bigint') {
    return input;
  }
  if (typeof input === 'number' && Number.isInteger(input)) {
    return BigInt(input);
  }
  if (typeof input === 'string') {
    // Reject empty or whitespace-only strings
    if (input.trim() === '') {
      return null;
    }
    try {
      return BigInt(input);
    } catch {
      return null;
    }
  }
  return null;
}

/**
 * Creates a validator for 64-bit integer values using BigInt
 * 
 * This corresponds to Avro's "long" type which represents 64-bit signed integers.
 * JavaScript's Number type cannot safely represent all 64-bit integers, so we use BigInt.
 * 
 * @param min - Minimum value (default: -2^63, Avro long minimum)
 * @param max - Maximum value (default: 2^63 - 1, Avro long maximum)
 * @returns A validator for bigint values within the specified range
 * 
 * @example
 * ```typescript
 * // Standard Avro long range
 * const longValue = Long();
 * longValue.validate(9007199254740993n); // ✅ valid (beyond Number.MAX_SAFE_INTEGER)
 * 
 * // Custom range
 * const positiveId = Long(1n, 1000000000000n);
 * 
 * // Accepts number inputs (converted to BigInt)
 * longValue.validate(42);      // ✅ valid, converted to 42n
 * longValue.validate("12345"); // ✅ valid, parsed to 12345n
 * ```
 */
export function Long(min: bigint = LONG_MIN, max: bigint = LONG_MAX): Validator<bigint> {
  if (min > max) {
    throw new Error('min must be less than or equal to max');
  }

  return {
    validate: (input: unknown): ValidationResult<bigint> => {
      const value = toBigInt(input);
      
      if (value === null) {
        return {
          valid: false,
          error: `Expected bigint, integer, or numeric string, got ${typeof input}`,
        };
      }

      if (value < min) {
        return {
          valid: false,
          error: `Value ${value} is less than minimum ${min}`,
        };
      }

      if (value > max) {
        return {
          valid: false,
          error: `Value ${value} is greater than maximum ${max}`,
        };
      }

      return { valid: true, value };
    },
    domain: bigIntDomain(min, max),
  };
}

