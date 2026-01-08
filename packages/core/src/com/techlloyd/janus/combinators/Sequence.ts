import { Validator, BaseValidator } from '../Validator';
import { ValidationResult, prependPath } from '../ValidationResult';
import { Domain, SequenceDomain } from '../Domain';
import { TupleOfValidators, DomainsForTuple } from '../Types';

/**
 * Generic Sequence combinator that validates an array of values against a list of validators.
 * 
 * Each element in the input array is validated against the corresponding validator
 * at the same index. The array must have exactly as many elements as there are validators.
 * 
 * On failure, returns a recursive ValidationResult with per-element results,
 * showing which elements passed and which failed (with examples at each level).
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
export class Sequence<
  Vs extends readonly Validator<unknown, Domain<unknown>>[] = readonly Validator<unknown, Domain<unknown>>[]
> extends BaseValidator<TupleOfValidators<Vs>, SequenceDomain<TupleOfValidators<Vs>>> {
  public readonly validators: Vs;
  public readonly domain: SequenceDomain<TupleOfValidators<Vs>>;

  constructor(...validators: [...Vs]) {
    super();
    this.validators = validators as Vs;
    const parts = validators.map((v) => v.domain as Domain<unknown>);
    this.domain = new SequenceDomain(parts);
  }

  /**
   * Validate an array by checking each element against its corresponding validator.
   * Returns recursive ValidationResult with per-element results.
   */
  validate(value: unknown): ValidationResult<TupleOfValidators<Vs>> {
    if (!Array.isArray(value)) {
      return this.error(`Expected array, got ${typeof value}`);
    }

    if (value.length !== this.validators.length) {
      return this.error(`Expected array of length ${this.validators.length}, got ${value.length}`);
    }

    const validatedValues: unknown[] = [];
    const results: ValidationResult<unknown>[] = [];
    let hasErrors = false;

    for (let i = 0; i < this.validators.length; i++) {
      const result = this.validators[i].validate(value[i]);
      
      // Prepend index to error path
      results.push(result.valid ? result : prependPath(result, i));
      
      if (!result.valid) {
        hasErrors = true;
      } else {
        validatedValues.push(result.value);
      }
    }

    if (hasErrors) {
      return this.arrayError(results);
    }

    return this.success(validatedValues as TupleOfValidators<Vs>);
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
  static of<Vs extends readonly Validator<unknown, Domain<unknown>>[]>(
    ...validators: Vs
  ): Sequence<Vs> {
    return new Sequence<Vs>(...validators);
  }
}
