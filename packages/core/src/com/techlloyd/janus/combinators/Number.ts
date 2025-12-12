import { BaseValidator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { ContiguousDomain, ContiguousType } from '../Domain';

/**
 * Validator for floating-point number values within an optional range.
 * 
 * @example
 * ```typescript
 * const percent = Number(0, 100);
 * percent.validate(50.5);   // valid
 * percent.validate(0);      // valid
 * percent.validate(-1);     // invalid (below min)
 * percent.validate(100.1);  // invalid (above max)
 * ```
 */
export class NumberValidator extends BaseValidator<number> {
  public readonly domain: ContiguousDomain;

  constructor(
    public readonly min: number = -globalThis.Number.MAX_VALUE,
    public readonly max: number = globalThis.Number.MAX_VALUE
  ) {
    super();
    this.domain = new ContiguousDomain(ContiguousType.FLOAT, min, max);
  }

  validate(input: unknown): ValidationResult<number> {
    if (typeof input !== 'number') {
      return this.error(`Expected number, got ${typeof input}`);
    }

    if (!globalThis.Number.isFinite(input)) {
      return this.error(`Expected finite number, got ${input}`);
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
 * Creates a validator for floating-point number values within an optional range.
 * @param min Minimum value (inclusive), defaults to -Number.MAX_VALUE
 * @param max Maximum value (inclusive), defaults to Number.MAX_VALUE
 */
export function Number(
  min: number = -globalThis.Number.MAX_VALUE,
  max: number = globalThis.Number.MAX_VALUE
): NumberValidator {
  return new NumberValidator(min, max);
}
