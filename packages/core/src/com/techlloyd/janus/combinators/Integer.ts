import { BaseValidator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { ContiguousDomain, ContiguousType } from '../Domain';

/**
 * Validator for integer values within an optional range.
 * 
 * @example
 * ```typescript
 * const age = Integer(0, 150);
 * age.validate(25);    // valid
 * age.validate(-1);    // invalid
 * age.validate(3.14);  // invalid (not integer)
 * ```
 */
export class IntegerValidator extends BaseValidator<number> {
  public readonly domain: ContiguousDomain;

  constructor(
    public readonly min: number = Number.MIN_SAFE_INTEGER,
    public readonly max: number = Number.MAX_SAFE_INTEGER
  ) {
    super();
    this.domain = new ContiguousDomain(ContiguousType.INTEGER, min, max);
  }

  validate(input: unknown): ValidationResult<number> {
    if (typeof input !== 'number') {
      return this.error(`Expected number, got ${typeof input}`);
    }

    if (!Number.isFinite(input)) {
      return this.error(`Expected finite number, got ${input}`);
    }

    if (!Number.isInteger(input)) {
      return this.error(`Expected integer, got ${input}`);
    }

    if (input < this.min) {
      return this.error(`Value ${input} is less than minimum ${this.min}`);
    }

    if (input > this.max) {
      return this.error(`Value ${input} is greater than maximum ${this.max}`);
    }

    return this.success(input);
  }
}

/**
 * Creates a validator for integer values within an optional range.
 * @param min Minimum value (inclusive), defaults to Number.MIN_SAFE_INTEGER
 * @param max Maximum value (inclusive), defaults to Number.MAX_SAFE_INTEGER
 */
export function Integer(
  min: number = Number.MIN_SAFE_INTEGER,
  max: number = Number.MAX_SAFE_INTEGER
): IntegerValidator {
  return new IntegerValidator(min, max);
}
