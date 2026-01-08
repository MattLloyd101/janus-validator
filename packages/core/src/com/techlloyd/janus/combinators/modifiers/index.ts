/**
 * Validator Modifiers
 * 
 * This module provides wrapper validators that modify the behavior of existing validators:
 * - optional() / .optional() - Accept undefined in addition to the normal type
 * - nullable() / .nullable() - Accept null in addition to the normal type
 * - nullish() / .nullish() - Accept null or undefined in addition to the normal type
 * - withDefault() / .default() - Provide a default value when input is undefined
 * - transform() / .transform() - Transform the validated value
 * - .trim(), .toLowerCase(), .toUpperCase() - Common string transforms
 * 
 * Each modifier uses composition, wrapping the inner validator without modifying it.
 * 
 * @example
 * ```typescript
 * // Standalone functions (tree-shakeable)
 * const maybeName = optional(UnicodeString(1, 50));
 * const port = withDefault(Integer(1, 65535), 3000);
 * const trimmed = transform(UnicodeString(), s => s.trim());
 * 
 * // Fluent methods (ergonomic)
 * const maybeName = UnicodeString(1, 50).optional();
 * const port = Integer(1, 65535).default(3000);
 * const normalized = UnicodeString().trim().toLowerCase();
 * ```
 */

import { BaseValidator, Validator } from '../../Validator';
import { Domain, AlternationDomain, TransformDomain } from '../../Domain';

// Export validators and standalone functions
export { OptionalValidator, optional } from './Optional';
export { NullableValidator, nullable } from './Nullable';
export { NullishValidator, nullish } from './Nullish';
export { DefaultValidator, withDefault } from './Default';
export { TransformValidator, transform } from './Transform';

// Import for prototype extension
import { OptionalValidator } from './Optional';
import { NullableValidator } from './Nullable';
import { NullishValidator } from './Nullish';
import { DefaultValidator } from './Default';
import { TransformValidator } from './Transform';

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

    /**
     * Transforms the validated value using the provided function.
     * 
     * The transform is applied after successful validation. If the transform
     * throws an error, it becomes a validation error.
     * 
     * Transforms are chainable - you can call .transform(), .trim(), etc. on the result.
     * 
     * @typeParam TOut The output type after transformation
     * @param fn The transformation function
     * @returns A new validator that produces transformed values
     * 
     * @example
     * ```typescript
     * // Basic transform
     * const trimmed = UnicodeString(1, 100).transform(s => s.trim());
     * trimmed.validate("  hello  "); // { valid: true, value: "hello" }
     * 
     * // Type-changing transform
     * const toInt = UnicodeString().transform(s => parseInt(s, 10));
     * toInt.validate("42"); // { valid: true, value: 42 }
     * 
     * // Chained transforms
     * const normalized = UnicodeString()
     *   .trim()
     *   .toLowerCase()
     *   .transform(s => s.replace(/\s+/g, '-'));
     * ```
     */
    transform<TOut>(fn: (value: T) => TOut): TransformValidator<T, TOut, D>;

    /**
     * Trims whitespace from both ends of a string value.
     * Only available on string validators. Chainable with other transforms.
     * 
     * @returns A new validator that trims the validated string
     * 
     * @example
     * ```typescript
     * const trimmed = UnicodeString(1, 100).trim();
     * trimmed.validate("  hello  "); // { valid: true, value: "hello" }
     * 
     * // Chain with other transforms
     * const normalized = UnicodeString().trim().toLowerCase();
     * ```
     */
    trim(): T extends string ? TransformValidator<string, string, D & Domain<string>> : never;

    /**
     * Converts a string value to lowercase.
     * Only available on string validators. Chainable with other transforms.
     * 
     * @returns A new validator that lowercases the validated string
     * 
     * @example
     * ```typescript
     * const lower = UnicodeString(1, 100).toLowerCase();
     * lower.validate("HELLO"); // { valid: true, value: "hello" }
     * 
     * // Chain with other transforms
     * const normalized = UnicodeString().trim().toLowerCase();
     * ```
     */
    toLowerCase(): T extends string ? TransformValidator<string, string, D & Domain<string>> : never;

    /**
     * Converts a string value to uppercase.
     * Only available on string validators. Chainable with other transforms.
     * 
     * @returns A new validator that uppercases the validated string
     * 
     * @example
     * ```typescript
     * const upper = UnicodeString(1, 100).toUpperCase();
     * upper.validate("hello"); // { valid: true, value: "HELLO" }
     * 
     * // Chain with other transforms
     * const normalized = UnicodeString().trim().toUpperCase();
     * ```
     */
    toUpperCase(): T extends string ? TransformValidator<string, string, D & Domain<string>> : never;
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

BaseValidator.prototype.transform = function<T, TOut, D extends Domain<T>>(
  this: Validator<T, D>,
  fn: (value: T) => TOut
): TransformValidator<T, TOut, D> {
  return new TransformValidator(this, fn);
};

// String convenience methods
BaseValidator.prototype.trim = function<D extends Domain<string>>(
  this: Validator<string, D>
): TransformValidator<string, string, D> {
  return new TransformValidator(this, (s: string) => s.trim());
};

BaseValidator.prototype.toLowerCase = function<D extends Domain<string>>(
  this: Validator<string, D>
): TransformValidator<string, string, D> {
  return new TransformValidator(this, (s: string) => s.toLowerCase());
};

BaseValidator.prototype.toUpperCase = function<D extends Domain<string>>(
  this: Validator<string, D>
): TransformValidator<string, string, D> {
  return new TransformValidator(this, (s: string) => s.toUpperCase());
};
