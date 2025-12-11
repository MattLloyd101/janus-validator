import { Validator } from '../Validator';
import { ValidationResult } from '../ValidationResult';

/**
 * Wraps a validator and asserts its output type as T.
 * 
 * This provides compile-time checking that your validator's inferred type
 * is assignable to your target interface, and the result is typed as T
 * without needing explicit casts.
 * 
 * @example
 * ```typescript
 * interface User {
 *   name: string;
 *   age: number;
 * }
 * 
 * // Without Typed - need to cast:
 * const v1 = O({ name: S(), age: I() });
 * const result1 = v1.validate(input);
 * if (result1.valid) {
 *   const user: User = result1.value; // Works but verbose
 * }
 * 
 * // With Typed - output is directly User:
 * const v2 = Typed<User>(O({ name: S(), age: I() }));
 * const result2 = v2.validate(input);
 * if (result2.valid) {
 *   result2.value.name; // TypeScript knows this is User
 * }
 * 
 * // Compile-time error if schema doesn't match interface:
 * const v3 = Typed<User>(O({ name: S() })); // Error: missing 'age'
 * ```
 */
export function Typed<T>() {
  /**
   * Returns a function that accepts a validator whose inferred type
   * must be assignable to T. This two-step approach allows TypeScript
   * to check the constraint properly.
   */
  return <V extends Validator<T>>(validator: V): Validator<T> => {
    return {
      validate: (input: unknown): ValidationResult<T> => {
        return validator.validate(input);
      },
      domain: validator.domain,
    };
  };
}

/**
 * Alternative: Type assertion that validates at compile-time that
 * the inferred type I is assignable to target type T.
 * 
 * @example
 * ```typescript
 * interface User { name: string; age: number; }
 * 
 * const userValidator = As<User>()(O({
 *   name: S(),
 *   age: I(),
 * }));
 * // userValidator is Validator<User>
 * ```
 */
export const As = Typed;

