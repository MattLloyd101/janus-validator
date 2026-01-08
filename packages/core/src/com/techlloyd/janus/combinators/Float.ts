import { BaseValidator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { ContiguousDomain, CustomGeneratorDomain } from '../Domain';

/**
 * Validator for floating-point number values within an optional range.
 * 
 * @example
 * ```typescript
 * const percent = Float(0, 100);
 * percent.validate(50.5);   // valid
 * percent.validate(0);      // valid
 * percent.validate(-1);     // invalid (below min)
 * percent.validate(100.1);  // invalid (above max)
 * ```
 */
export class FloatValidator extends BaseValidator<number> {
  public readonly domain: CustomGeneratorDomain<number, ContiguousDomain<number>>;

  constructor(
    public readonly min: number = -Number.MAX_VALUE,
    public readonly max: number = Number.MAX_VALUE
  ) {
    super();
    const innerDomain = new ContiguousDomain(min, max);
    this.domain = new CustomGeneratorDomain(innerDomain, (rng) => {
      const range = max - min;
      return min + rng.random() * range;
    });
  }

  validate(input: unknown): ValidationResult<number> {
    if (typeof input !== 'number') {
      return this.error(`Expected number, got ${typeof input}`);
    }

    if (!Number.isFinite(input)) {
      return this.error(`Expected finite number, got ${input}`);
    }

    if (input < this.min) {
      return this.error(`Expected value >= ${this.min}, got ${input}`);
    }

    if (input > this.max) {
      return this.error(`Expected value <= ${this.max}, got ${input}`);
    }

    return this.success(input);
  }
}

/**
 * Creates a validator for floating-point number values within an optional range.
 * @param min Minimum value (inclusive), defaults to -Number.MAX_VALUE
 * @param max Maximum value (inclusive), defaults to Number.MAX_VALUE
 */
export function Float(
  min: number = -Number.MAX_VALUE,
  max: number = Number.MAX_VALUE
): FloatValidator {
  return new FloatValidator(min, max);
}

