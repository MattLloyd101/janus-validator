import { ConstantValidator, Constant } from './Constant';

/**
 * Creates a validator for NaN (Not a Number)
 * 
 * Uses a custom comparator since NaN !== NaN in JavaScript.
 * 
 * @example
 * ```typescript
 * const validator = NaN();
 * validator.validate(NaN);        // valid
 * validator.validate(0/0);        // valid
 * validator.validate(undefined);  // invalid
 * validator.validate(0);          // invalid
 * ```
 */
export function NaN(): ConstantValidator<number> {
  return Constant(
    Number.NaN,
    (input) => typeof input === 'number' && Number.isNaN(input),
    'NaN'
  );
}
