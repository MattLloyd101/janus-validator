import { Validator, ValidationResult, FiniteDomain, DomainType } from '../index';

/**
 * Creates a validator for a single constant value.
 * 
 * This is the base for all fixed-value validators like Null, Undefined, NaN, Infinity, etc.
 * 
 * @param value The exact value to validate against
 * @param comparator Optional custom comparison function (defaults to ===)
 * @param displayName Optional name for error messages (defaults to String(value))
 * 
 * @example
 * ```typescript
 * const fortyTwo = Constant(42);
 * fortyTwo.validate(42);   // valid
 * fortyTwo.validate(43);   // invalid
 * 
 * const mySymbol = Constant(Symbol.for('my-symbol'));
 * ```
 */
export function Constant<T>(
  value: T,
  comparator: (input: unknown, value: T) => boolean = (input, val) => input === val,
  displayName: string = String(value)
): Validator<T> {
  return {
    validate: (input: unknown): ValidationResult<T> => {
      if (comparator(input, value)) {
        return { valid: true, value };
      }
      return {
        valid: false,
        error: `Expected ${displayName}, got ${formatValue(input)}`,
      };
    },
    domain: {
      type: DomainType.FINITE_DOMAIN,
      values: [value],
    } as FiniteDomain<T>,
  };
}

/**
 * Format a value for error messages
 */
function formatValue(input: unknown): string {
  if (input === null) return 'null';
  if (input === undefined) return 'undefined';
  if (typeof input === 'number' && Number.isNaN(input)) return 'NaN';
  if (input === Number.POSITIVE_INFINITY) return 'Infinity';
  if (input === Number.NEGATIVE_INFINITY) return '-Infinity';
  if (typeof input === 'string') return `"${input}"`;
  return String(input);
}

