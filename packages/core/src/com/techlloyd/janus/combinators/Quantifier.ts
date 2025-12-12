import { Validator, BaseValidator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { QuantifierDomain } from '../Domain';

/**
 * Generic Quantifier combinator that validates arrays of values.
 * 
 * Validates that an array has between `min` and `max` elements,
 * where each element passes the inner validator.
 * 
 * On failure, returns a recursive ValidationResult with per-element results,
 * showing which elements passed and which failed (with examples at each level).
 * 
 * @example
 * ```typescript
 * // Array of 1-5 integers between 0-100
 * const validator = new Quantifier(Integer(0, 100), 1, 5);
 * validator.validate([10, 20, 30]);    // valid (3 elements, all in range)
 * validator.validate([]);               // invalid (too few)
 * validator.validate([1,2,3,4,5,6]);   // invalid (too many)
 * validator.validate([10, 200, 30]);   // invalid (200 out of range)
 * ```
 */
export class Quantifier<T> extends BaseValidator<T[]> {
  public readonly domain: QuantifierDomain<T>;

  constructor(
    public readonly validator: Validator<T>,
    public readonly min: number,
    public readonly max: number
  ) {
    super();
    this.domain = new QuantifierDomain(validator.domain, min, max);
  }

  /**
   * Validate an array, checking length and each element.
   * Returns recursive ValidationResult with per-element results.
   */
  validate(value: unknown): ValidationResult<T[]> {
    if (!Array.isArray(value)) {
      return this.error(`Expected array, got ${typeof value}`);
    }

    if (value.length < this.min) {
      return this.error(`Expected at least ${this.min} elements, got ${value.length}`);
    }

    if (value.length > this.max) {
      return this.error(`Expected at most ${this.max} elements, got ${value.length}`);
    }

    const validatedValues: T[] = [];
    const results: ValidationResult<T>[] = [];
    let hasErrors = false;

    for (let i = 0; i < value.length; i++) {
      const result = this.validator.validate(value[i]);
      results.push(result);
      
      if (!result.valid) {
        hasErrors = true;
      } else {
        validatedValues.push(result.value);
      }
    }

    if (hasErrors) {
      return this.arrayError(results);
    }

    return this.success(validatedValues);
  }

  /**
   * Factory methods for common quantifiers
   */
  static zeroOrMore<T>(validator: Validator<T>): Quantifier<T> {
    return new Quantifier(validator, 0, Infinity);
  }

  static oneOrMore<T>(validator: Validator<T>): Quantifier<T> {
    return new Quantifier(validator, 1, Infinity);
  }

  static optional<T>(validator: Validator<T>): Quantifier<T> {
    return new Quantifier(validator, 0, 1);
  }

  static exactly<T>(validator: Validator<T>, n: number): Quantifier<T> {
    return new Quantifier(validator, n, n);
  }

  static atLeast<T>(validator: Validator<T>, n: number): Quantifier<T> {
    return new Quantifier(validator, n, Infinity);
  }

  static between<T>(validator: Validator<T>, min: number, max: number): Quantifier<T> {
    return new Quantifier(validator, min, max);
  }
}
