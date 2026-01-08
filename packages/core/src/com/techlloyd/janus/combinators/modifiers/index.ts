/**
 * Validator Modifiers
 * 
 * This module provides wrapper validators that modify the behavior of existing validators:
 * - optional() / .optional() - Accept undefined in addition to the normal type
 * - nullable() / .nullable() - Accept null in addition to the normal type
 * - nullish() / .nullish() - Accept null or undefined in addition to the normal type
 * - withDefault() / .default() - Provide a default value when input is undefined
 * 
 * Each modifier uses composition, wrapping the inner validator without modifying it.
 * 
 * @example
 * ```typescript
 * // Standalone functions (tree-shakeable)
 * const maybeName = optional(UnicodeString(1, 50));
 * const port = withDefault(Integer(1, 65535), 3000);
 * 
 * // Fluent methods (ergonomic)
 * const maybeName = UnicodeString(1, 50).optional();
 * const port = Integer(1, 65535).default(3000);
 * ```
 */

import { BaseValidator, Validator } from '../../Validator';
import { Domain, AlternationDomain } from '../../Domain';

// Export validators and standalone functions
export { OptionalValidator, optional } from './Optional';
export { NullableValidator, nullable } from './Nullable';
export { NullishValidator, nullish } from './Nullish';
export { DefaultValidator, withDefault } from './Default';

// Import for prototype extension
import { OptionalValidator } from './Optional';
import { NullableValidator } from './Nullable';
import { NullishValidator } from './Nullish';
import { DefaultValidator } from './Default';

// =============================================================================
// Fluent API via Prototype Extension
// =============================================================================

/**
 * Extend BaseValidator with modifier methods.
 * 
 * This allows the fluent API: validator.optional(), validator.nullable(), etc.
 */

// Type declarations for the extended interface
declare module '../../Validator' {
  interface BaseValidator<T, D extends Domain<T>> {
    /**
     * Makes this validator accept undefined in addition to its normal type.
     * 
     * @returns A new validator that accepts T | undefined
     * 
     * @example
     * ```typescript
     * const maybeName = UnicodeString(1, 50).optional();
     * maybeName.validate("Alice");    // valid
     * maybeName.validate(undefined);  // valid
     * ```
     */
    optional(): Validator<T | undefined, AlternationDomain<T | undefined>>;

    /**
     * Makes this validator accept null in addition to its normal type.
     * 
     * @returns A new validator that accepts T | null
     * 
     * @example
     * ```typescript
     * const nullableName = UnicodeString(1, 50).nullable();
     * nullableName.validate("Alice");  // valid
     * nullableName.validate(null);     // valid
     * ```
     */
    nullable(): Validator<T | null, AlternationDomain<T | null>>;

    /**
     * Makes this validator accept null or undefined in addition to its normal type.
     * 
     * @returns A new validator that accepts T | null | undefined
     * 
     * @example
     * ```typescript
     * const nullishName = UnicodeString(1, 50).nullish();
     * nullishName.validate("Alice");    // valid
     * nullishName.validate(null);       // valid
     * nullishName.validate(undefined);  // valid
     * ```
     */
    nullish(): Validator<T | null | undefined, AlternationDomain<T | null | undefined>>;

    /**
     * Provides a default value when input is undefined.
     * 
     * @param value Default value (static) or factory function (dynamic)
     * @returns A new validator that uses the default for undefined inputs
     * 
     * @example
     * ```typescript
     * // Static default
     * const port = Integer(1, 65535).default(3000);
     * port.validate(undefined); // { valid: true, value: 3000 }
     * 
     * // Dynamic default
     * const timestamp = Integer().default(() => Date.now());
     * ```
     */
    default(value: T | (() => T)): Validator<T, D>;
  }
}

// Implementation via prototype extension
BaseValidator.prototype.optional = function<T, D extends Domain<T>>(
  this: Validator<T, D>
): Validator<T | undefined, AlternationDomain<T | undefined>> {
  return new OptionalValidator(this);
};

BaseValidator.prototype.nullable = function<T, D extends Domain<T>>(
  this: Validator<T, D>
): Validator<T | null, AlternationDomain<T | null>> {
  return new NullableValidator(this);
};

BaseValidator.prototype.nullish = function<T, D extends Domain<T>>(
  this: Validator<T, D>
): Validator<T | null | undefined, AlternationDomain<T | null | undefined>> {
  return new NullishValidator(this);
};

BaseValidator.prototype.default = function<T, D extends Domain<T>>(
  this: Validator<T, D>,
  value: T | (() => T)
): Validator<T, D> {
  return new DefaultValidator(this, value);
};
