import { Validator } from '../index';
import { Constant } from './Constant';

/**
 * Creates a validator for null
 * 
 * @example
 * ```typescript
 * const validator = Null();
 * validator.validate(null);       // valid
 * validator.validate(undefined);  // invalid
 * validator.validate(0);          // invalid
 * validator.validate('');         // invalid
 * ```
 */
export function Null(): Validator<null> {
  return Constant(null, (input) => input === null, 'null');
}
