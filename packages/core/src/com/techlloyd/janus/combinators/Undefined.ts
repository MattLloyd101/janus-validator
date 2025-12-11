import { Validator } from '../index';
import { Constant } from './Constant';

/**
 * Creates a validator for undefined
 * 
 * @example
 * ```typescript
 * const validator = Undefined();
 * validator.validate(undefined);  // valid
 * validator.validate(void 0);     // valid
 * validator.validate(null);       // invalid
 * validator.validate(0);          // invalid
 * ```
 */
export function Undefined(): Validator<undefined> {
  return Constant(undefined, (input) => input === undefined, 'undefined');
}
