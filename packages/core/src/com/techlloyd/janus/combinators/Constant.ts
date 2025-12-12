import { BaseValidator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { FiniteDomain, DomainType } from '../Domain';

/**
 * Validator for a single constant value.
 * 
 * @example
 * ```typescript
 * const fortyTwo = Constant(42);
 * fortyTwo.validate(42);   // valid
 * fortyTwo.validate(43);   // invalid
 * ```
 */
export class ConstantValidator<T> extends BaseValidator<T> {
  public readonly domain: FiniteDomain<T>;

  constructor(
    public readonly value: T,
    public readonly comparator: (input: unknown, value: T) => boolean = (input, val) => input === val,
    public readonly displayName: string = String(value)
  ) {
    super();
    this.domain = {
      type: DomainType.FINITE_DOMAIN,
      values: [value],
    };
  }

  validate(input: unknown): ValidationResult<T> {
    if (this.comparator(input, this.value)) {
      return this.success(this.value);
    }
    return this.error(`Expected ${this.displayName}, got ${this.formatValue(input)}`);
  }
}

/**
 * Creates a validator for a single constant value.
 */
export function Constant<T>(
  value: T,
  comparator?: (input: unknown, value: T) => boolean,
  displayName?: string
): ConstantValidator<T> {
  return new ConstantValidator(value, comparator, displayName);
}
