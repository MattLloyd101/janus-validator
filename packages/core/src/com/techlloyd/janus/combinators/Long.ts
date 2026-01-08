import { BaseValidator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { BigIntDomain } from '../Domain';

const LONG_MIN = -(2n ** 63n);
const LONG_MAX = 2n ** 63n - 1n;

/**
 * Validator for 64-bit integer values using BigInt.
 * 
 * @example
 * ```typescript
 * const longValue = Long();
 * longValue.validate(9007199254740993n); // valid
 * longValue.validate(42);                // valid (converted)
 * longValue.validate("12345");           // valid (parsed)
 * ```
 */
export class LongValidator extends BaseValidator<bigint> {
  public readonly domain: BigIntDomain;

  constructor(
    public readonly min: bigint = LONG_MIN,
    public readonly max: bigint = LONG_MAX
  ) {
    super();
    if (min > max) {
      throw new Error('min must be less than or equal to max');
    }
    this.domain = new BigIntDomain(min, max);
  }

  /**
   * Converts various input types to BigInt if possible.
   */
  private toBigInt(input: unknown): bigint | null {
    if (typeof input === 'bigint') {
      return input;
    }
    if (typeof input === 'number' && Number.isInteger(input)) {
      return BigInt(input);
    }
    if (typeof input === 'string') {
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

  validate(input: unknown): ValidationResult<bigint> {
    const value = this.toBigInt(input);
    
    if (value === null) {
      return this.error(`Expected bigint, integer, or numeric string, got ${typeof input}`);
    }

    if (value < this.min) {
      return this.error(`Expected value >= ${this.min}, got ${value}`);
    }

    if (value > this.max) {
      return this.error(`Expected value <= ${this.max}, got ${value}`);
    }

    return this.success(value);
  }
}

/**
 * Creates a validator for 64-bit integer values using BigInt.
 */
export function Long(min: bigint = LONG_MIN, max: bigint = LONG_MAX): LongValidator {
  return new LongValidator(min, max);
}
