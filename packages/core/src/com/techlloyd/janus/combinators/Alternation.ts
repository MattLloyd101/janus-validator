import { Validator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { Domain, AlternationDomain, DomainType } from '../Domain';
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
export class Alternation<T, D extends Domain<T> = AlternationDomain<T>> implements Validator<T> {
  public readonly validators: Validator<any>[];
  protected readonly _domain: D;

  constructor(...validators: Validator<any>[]) {
    this.validators = validators;
    this._domain = {
      type: DomainType.ALTERNATION_DOMAIN,
      alternatives: validators.map(v => v.domain),
    } as unknown as D;
  }

  get domain(): D {
    return this._domain;
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

    return {
      valid: false,
      error: `Value did not match any alternative: ${errors.join('; ')}`,
    };
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
  static of<Vs extends readonly Validator<any>[]>(
    ...validators: Vs
  ): Validator<UnionOfValidators<Vs>> {
    if (validators.length === 0) {
      throw new Error('Alternation requires at least one validator');
    }
    if (validators.length === 1) {
      return validators[0] as Validator<UnionOfValidators<Vs>>;
    }
    return new Alternation<UnionOfValidators<Vs>>(...validators);
  }
}

