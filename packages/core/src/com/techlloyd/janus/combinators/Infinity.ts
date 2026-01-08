import { ConstantValidator, Constant } from './Constant';

/**
 * Creates a validator for positive Infinity
 * 
 * @example
 * ```typescript
 * const validator = Infinity();
 * validator.validate(Infinity);   // valid
 * validator.validate(-Infinity);  // invalid
 * validator.validate(1000);       // invalid
 * ```
 */
export function Infinity(): ConstantValidator<number> {
  return Constant(Number.POSITIVE_INFINITY, (input, val) => input === val, 'Infinity');
}

/**
 * Creates a validator for negative Infinity
 * 
 * @example
 * ```typescript
 * const validator = NegativeInfinity();
 * validator.validate(-Infinity);  // valid
 * validator.validate(Infinity);   // invalid
 * validator.validate(-1000);      // invalid
 * ```
 */
export function NegativeInfinity(): ConstantValidator<number> {
  return Constant(Number.NEGATIVE_INFINITY, (input, val) => input === val, '-Infinity');
}
