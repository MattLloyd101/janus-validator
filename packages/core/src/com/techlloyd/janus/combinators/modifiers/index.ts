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
 * - refine() / .refine() - Add custom validation predicates
 * - superRefine() / .superRefine() - Complex validation with multiple issues
 * - message() / .message() - Override error messages
 * - code() / .code() - Add error codes for i18n
 * - describe() / .describe() - Add descriptions for documentation
 * 
 * Each modifier uses composition, wrapping the inner validator without modifying it.
 * 
 * @example
 * ```typescript
 * // Standalone functions (tree-shakeable)
 * const maybeName = optional(UnicodeString(1, 50));
 * const port = withDefault(Integer(1, 65535), 3000);
 * const trimmed = transform(UnicodeString(), s => s.trim());
 * const even = refine(Integer(0, 100), n => n % 2 === 0, 'Must be even');
 * 
 * // Fluent methods (ergonomic)
 * const maybeName = UnicodeString(1, 50).optional();
 * const port = Integer(1, 65535).default(3000);
 * const normalized = UnicodeString().trim().toLowerCase();
 * 
 * // Error customization
 * const email = UnicodeString(5, 100)
 *   .refine(s => s.includes('@'), 'Invalid email')
 *   .message('Please enter a valid email address')
 *   .code('INVALID_EMAIL')
 *   .describe('User email for account recovery');
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
export { RefineValidator, refine } from './Refine';
export { 
  SuperRefineValidator, 
  superRefine, 
  RefinementContext, 
  RefinementIssue 
} from './SuperRefine';
export { MessageValidator, message } from './Message';
export { CodeValidator, code } from './Code';
export { DescribeValidator, describe } from './Describe';

// Import for prototype extension
import { OptionalValidator } from './Optional';
import { NullableValidator } from './Nullable';
import { NullishValidator } from './Nullish';
import { DefaultValidator } from './Default';
import { TransformValidator } from './Transform';
import { RefineValidator } from './Refine';
import { SuperRefineValidator, RefinementContext } from './SuperRefine';
import { MessageValidator } from './Message';
import { CodeValidator } from './Code';
import { DescribeValidator } from './Describe';

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

    // =========================================================================
    // Refinements
    // =========================================================================

    /**
     * Adds a custom validation predicate.
     * 
     * The refinement runs after the inner validator succeeds.
     * **Note:** Refinements do NOT affect the domain - generated values may fail refinement.
     * 
     * @param predicate Function returning true if valid
     * @param message Error message (string or function)
     * @returns A new validator with the additional check
     * 
     * @example
     * ```typescript
     * // Simple predicate
     * const even = Integer(0, 100).refine(n => n % 2 === 0, 'Must be even');
     * 
     * // Dynamic message
     * const positive = Float().refine(
     *   n => n > 0,
     *   n => `Expected positive, got ${n}`
     * );
     * 
     * // Chained refinements
     * const password = UnicodeString(8, 100)
     *   .refine(s => /[A-Z]/.test(s), 'Must contain uppercase')
     *   .refine(s => /[0-9]/.test(s), 'Must contain digit');
     * ```
     */
    refine(
      predicate: (value: T) => boolean,
      message?: string | ((value: T) => string)
    ): RefineValidator<T, D>;

    /**
     * Adds complex validation with multiple potential issues.
     * 
     * Use this when you need to report multiple validation issues at once
     * or when validation logic is complex.
     * 
     * @param check Function that calls ctx.addIssue() for problems
     * @returns A new validator that collects all issues
     * 
     * @example
     * ```typescript
     * const password = UnicodeString(8, 100).superRefine((s, ctx) => {
     *   if (!/[A-Z]/.test(s)) ctx.addIssue({ message: 'Need uppercase' });
     *   if (!/[0-9]/.test(s)) ctx.addIssue({ message: 'Need digit' });
     * });
     * 
     * // Cross-field validation
     * const form = Struct({
     *   password: UnicodeString(8, 100),
     *   confirm: UnicodeString(8, 100),
     * }).superRefine((value, ctx) => {
     *   if (value.password !== value.confirm) {
     *     ctx.addIssue({ message: 'Passwords must match', path: ['confirm'] });
     *   }
     * });
     * ```
     */
    superRefine(check: (value: T, ctx: RefinementContext) => void): SuperRefineValidator<T, D>;

    // =========================================================================
    // Convenience Refinements - Numbers
    // =========================================================================

    /**
     * Requires the number to be a multiple of n.
     * Only available on number validators.
     * 
     * @param n The divisor
     * @param message Optional custom error message
     * @example Integer(0, 100).multipleOf(5) // 0, 5, 10, 15...
     */
    multipleOf(n: number, message?: string): T extends number ? RefineValidator<number, D & Domain<number>> : never;


    // =========================================================================
    // Convenience Refinements - Strings
    // =========================================================================

    /**
     * Validates the string includes a substring.
     * Only available on string validators.
     * 
     * @param substring The required substring
     * @param message Optional custom error message
     * @example UnicodeString().includes('@')
     */
    includes(substring: string, message?: string): T extends string ? RefineValidator<string, D & Domain<string>> : never;

    // =========================================================================
    // Error Customization
    // =========================================================================

    /**
     * Override the error message for this validator.
     * 
     * @param msg Static message or function (originalError, value) => message
     * @returns A new validator with the custom message
     * 
     * @example
     * ```typescript
     * // Static message
     * const age = Integer(0, 150).message('Please enter a valid age');
     * 
     * // Dynamic message
     * const count = Integer(1, 100).message((err, val) => 
     *   `Invalid count "${val}": ${err}`
     * );
     * ```
     */
    message(msg: string | ((error: string, value: unknown) => string)): MessageValidator<T, D>;

    /**
     * Add an error code for i18n or programmatic handling.
     * 
     * Error codes are useful for:
     * - Translating error messages to different languages
     * - Programmatically handling specific error types
     * - Logging and analytics
     * 
     * @param errorCode The error code to attach
     * @returns A new validator that includes the error code on failure
     * 
     * @example
     * ```typescript
     * const email = UnicodeString(5, 100)
     *   .refine(s => s.includes('@'))
     *   .code('INVALID_EMAIL');
     * 
     * const result = email.validate('bad');
     * if (!result.valid) {
     *   console.log(result.code); // 'INVALID_EMAIL'
     * }
     * ```
     */
    code(errorCode: string): CodeValidator<T, D>;

    /**
     * Add a description for documentation.
     * 
     * Descriptions are useful for:
     * - Auto-generating API documentation
     * - Showing tooltips or help text in forms
     * - Understanding what a validator is for
     * 
     * @param description Human-readable description
     * @returns A new validator with the description attached
     * 
     * @example
     * ```typescript
     * const email = UnicodeString(5, 100)
     *   .describe('User email address for account recovery');
     * 
     * console.log(email.description); // 'User email address...'
     * ```
     */
    describe(description: string): DescribeValidator<T, D>;
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

// =============================================================================
// Refinement Methods
// =============================================================================

BaseValidator.prototype.refine = function<T, D extends Domain<T>>(
  this: Validator<T, D>,
  predicate: (value: T) => boolean,
  message: string | ((value: T) => string) = 'Refinement failed'
): RefineValidator<T, D> {
  return new RefineValidator(this, predicate, message);
};

BaseValidator.prototype.superRefine = function<T, D extends Domain<T>>(
  this: Validator<T, D>,
  check: (value: T, ctx: RefinementContext) => void
): SuperRefineValidator<T, D> {
  return new SuperRefineValidator(this, check);
};

// =============================================================================
// Numeric Refinements
// =============================================================================

BaseValidator.prototype.multipleOf = function<D extends Domain<number>>(
  this: Validator<number, D>,
  n: number,
  message?: string
): RefineValidator<number, D> {
  return new RefineValidator(
    this, 
    (v: number) => v % n === 0, 
    message ?? `Must be a multiple of ${n}`
  );
};

// =============================================================================
// String Refinements
// =============================================================================

BaseValidator.prototype.includes = function<D extends Domain<string>>(
  this: Validator<string, D>,
  substring: string,
  message?: string
): RefineValidator<string, D> {
  return new RefineValidator(
    this,
    (s: string) => s.includes(substring),
    message ?? `Must include "${substring}"`
  );
};

// =============================================================================
// Error Customization Methods
// =============================================================================

BaseValidator.prototype.message = function<T, D extends Domain<T>>(
  this: Validator<T, D>,
  msg: string | ((error: string, value: unknown) => string)
): MessageValidator<T, D> {
  return new MessageValidator(this, msg);
};

BaseValidator.prototype.code = function<T, D extends Domain<T>>(
  this: Validator<T, D>,
  errorCode: string
): CodeValidator<T, D> {
  return new CodeValidator(this, errorCode);
};

BaseValidator.prototype.describe = function<T, D extends Domain<T>>(
  this: Validator<T, D>,
  description: string
): DescribeValidator<T, D> {
  return new DescribeValidator(this, description);
};
