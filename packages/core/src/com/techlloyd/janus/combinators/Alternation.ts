import { Validator, BaseValidator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { Domain, AlternationDomain } from '../Domain';
import { UnionOfValidators } from '../Types';

/**
 * Generic Alternation combinator that matches any one of its child validators.
 * 
 * This is a core combinator that can work with any validator type.
 * The validation succeeds if any of the alternative validators succeeds.
 * Generation picks one alternative at random and generates from it.
 * 
 * The type is automatically inferred as a union of all validator types:
 * 
 * @example
 * ```typescript
 * // Type is inferred as Validator<string | number | null>
 * const validator = Alternation.of(UnicodeString(), Integer(), Null());
 * 
 * // Match either a small integer or a large integer
 * const intValidator = new Alternation(Integer(0, 10), Integer(100, 200));
 * intValidator.validate(5);   // valid
 * intValidator.validate(150); // valid
 * intValidator.validate(50);  // invalid
 * ```
 */
export class Alternation<T, D extends Domain<T> = AlternationDomain<T>> extends BaseValidator<T, D> {
  public readonly validators: Validator<unknown, Domain<unknown>>[];
  public readonly domain: D;

  constructor(validators: Validator<unknown, Domain<unknown>>[], domainOverride?: D);
  constructor(...validators: Validator<unknown, Domain<unknown>>[]);
  constructor(...args: [Validator<unknown, Domain<unknown>>[], D?] | Validator<unknown, Domain<unknown>>[]) {
    super();
    // Handle both overloads
    if (Array.isArray(args[0]) && (args.length === 1 || args.length === 2)) {
      // Called with (validators[], domain?)
      this.validators = args[0] as Validator<unknown, Domain<unknown>>[];
      const domainOverride = args[1] as D | undefined;
      this.domain = domainOverride ?? new AlternationDomain(this.validators.map(v => v.domain)) as unknown as D;
    } else {
      // Called with (...validators)
      this.validators = args as Validator<unknown, Domain<unknown>>[];
      this.domain = new AlternationDomain(this.validators.map(v => v.domain)) as unknown as D;
    }
  }

  /**
   * Validate by trying each alternative in order, returning first success
   */
  validate(value: unknown): ValidationResult<T> {
    const errors: string[] = [];

    for (const validator of this.validators) {
      const result = validator.validate(value);
      if (result.valid) {
        return result as ValidationResult<T>;
      }
      if (!result.valid) {
        errors.push(result.error);
      }
    }

    return this.error(`Value did not match any alternative: ${errors.join('; ')}`);
  }

  /**
   * Factory method to create an alternation with proper union type inference.
   * 
   * @example
   * ```typescript
   * // Type is Validator<string | number | null>
   * const v = Alternation.of(UnicodeString(), Integer(), Null());
   * ```
   */
  static of<Vs extends readonly Validator<unknown, Domain<unknown>>[]>(
    ...validators: Vs
  ): Validator<UnionOfValidators<Vs>, AlternationDomain<UnionOfValidators<Vs>>> {
    if (validators.length === 0) {
      throw new Error('Alternation requires at least one validator');
    }
    if (validators.length === 1) {
      return validators[0] as Validator<UnionOfValidators<Vs>, AlternationDomain<UnionOfValidators<Vs>>>;
    }
    return new Alternation<UnionOfValidators<Vs>>(...validators);
  }
}
