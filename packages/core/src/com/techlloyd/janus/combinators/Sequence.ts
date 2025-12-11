import { Validator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { SequenceDomain, DomainType } from '../Domain';
import { TupleOfValidators } from '../Types';

/**
 * Generic Sequence combinator that validates an array of values against a list of validators.
 * 
 * Each element in the input array is validated against the corresponding validator
 * at the same index. The array must have exactly as many elements as there are validators.
 * 
 * The tuple type is automatically inferred from the validators:
 * 
 * @example
 * ```typescript
 * // Type is inferred as Validator<[number, string, boolean]>
 * const validator = Sequence.of(Integer(0, 100), UnicodeString(1, 5), Boolean());
 * 
 * validator.validate([50, "abc", true]);  // valid
 * validator.validate([50]);               // invalid (wrong length)
 * 
 * const result = validator.validate([42, "hi", false]);
 * if (result.valid) {
 *   const [num, str, bool] = result.value;  // TypeScript knows the types!
 * }
 * ```
 */
export class Sequence<T extends any[] = any[]> implements Validator<T> {
  public readonly validators: Validator<any>[];
  protected readonly _domain: SequenceDomain<any>;

  constructor(...validators: Validator<any>[]) {
    this.validators = validators;
    this._domain = {
      type: DomainType.SEQUENCE_DOMAIN,
      parts: validators.map(v => v.domain),
    };
  }

  get domain(): SequenceDomain<any> {
    return this._domain;
  }

  /**
   * Validate an array by checking each element against its corresponding validator
   */
  validate(value: unknown): ValidationResult<T> {
    if (!Array.isArray(value)) {
      return {
        valid: false,
        error: `Expected array, got ${typeof value}`,
      };
    }

    if (value.length !== this.validators.length) {
      return {
        valid: false,
        error: `Expected array of length ${this.validators.length}, got ${value.length}`,
      };
    }

    const validatedValues: any[] = [];

    for (let i = 0; i < this.validators.length; i++) {
      const result = this.validators[i].validate(value[i]);
      if (!result.valid) {
        return {
          valid: false,
          error: `Element at index ${i}: ${result.error}`,
        };
      }
      validatedValues.push(result.value);
    }

    return { valid: true, value: validatedValues as T };
  }

  /**
   * Factory method to create a sequence with proper tuple type inference.
   * 
   * @example
   * ```typescript
   * // Type is Validator<[string, number, boolean]>
   * const v = Sequence.of(UnicodeString(), Integer(), Boolean());
   * ```
   */
  static of<Vs extends readonly Validator<any>[]>(
    ...validators: Vs
  ): Validator<TupleOfValidators<Vs> & any[]> {
    return new Sequence<TupleOfValidators<Vs> & any[]>(...validators);
  }
}

