import { Validator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { QuantifierDomain, DomainType } from '../Domain';

/**
 * Default maximum repetitions for unbounded quantifiers when generating
 */
const DEFAULT_MAX_UNBOUNDED = 10;

/**
 * Generic Quantifier combinator that validates arrays of values.
 * 
 * Validates that an array has between `min` and `max` elements,
 * where each element passes the inner validator.
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
export class Quantifier<T> implements Validator<T[]> {
  public readonly _domain: QuantifierDomain<T>;

  constructor(
    public readonly validator: Validator<T>,
    public readonly min: number,
    public readonly max: number,
    public readonly maxUnbounded: number = DEFAULT_MAX_UNBOUNDED
  ) {
    this._domain = {
      type: DomainType.QUANTIFIER_DOMAIN,
      inner: validator.domain,
      min,
      max,
    };
  }

  get domain(): QuantifierDomain<T> {
    return this._domain;
  }

  /**
   * Validate an array, checking length and each element
   */
  validate(value: unknown): ValidationResult<T[]> {
    if (!Array.isArray(value)) {
      return {
        valid: false,
        error: `Expected array, got ${typeof value}`,
      };
    }

    if (value.length < this.min) {
      return {
        valid: false,
        error: `Expected at least ${this.min} elements, got ${value.length}`,
      };
    }

    if (value.length > this.max) {
      return {
        valid: false,
        error: `Expected at most ${this.max} elements, got ${value.length}`,
      };
    }

    const validatedValues: T[] = [];

    for (let i = 0; i < value.length; i++) {
      const result = this.validator.validate(value[i]);
      if (!result.valid) {
        return {
          valid: false,
          error: `Element at index ${i}: ${result.error}`,
        };
      }
      validatedValues.push(result.value);
    }

    return { valid: true, value: validatedValues };
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

