/**
 * DSL - Short aliases for all combinators
 * 
 * Examples are automatically included on validation errors by core validators.
 * 
 * @example
 * ```typescript
 * import { B, S, I, N, L, R, O, Bytes, Or, Seq, optional, oneOrMore } from './DSL';
 * 
 * // Simple validators
 * const isBoolean = B();
 * const isString = U(1, 100);
 * const isInteger = I(0, 100);
 * const isLong = L();  // 64-bit bigint
 * const isBinary = Bytes(0, 1024);
 * 
 * // Object schema
 * const user = O({
 *   name: U(1, 50),
 *   age: I(0, 150),
 *   active: B()
 * });
 * 
 * // Regex
 * const email = R(/^[\w.]+@[\w.]+\.\w+$/);
 * 
 * // Combinators
 * const stringOrNumber = Or(U(), N());
 * const tags = oneOrMore(U(1, 20));
 * ```
 */

import {
  Validator,
  Domain,
  Boolean as BooleanValidator,
  UnicodeString as UnicodeStringValidator,
  CompoundString as CompoundStringValidator,
  digits as digitsValidator,
  lower as lowerValidator,
  upper as upperValidator,
  letters as lettersValidator,
  alphanumeric as alphanumericValidator,
  hex as hexValidator,
  hexUpper as hexUpperValidator,
  chars as charsValidator,
  Integer as IntegerValidator,
  Float as FloatValidator,
  Regex as RegexValidator,
  Struct as StructValidator,
  StructSchema,
  Constant as ConstantValidator,
  Alternation as AlternationValidator,
  Sequence as SequenceValidator,
  Quantifier as QuantifierValidator,
  Null as NullValidator,
  Undefined as UndefinedValidator,
  Infinity as InfinityValidator,
  NegativeInfinity as NegativeInfinityValidator,
  NaN as NaNValidator,
  Bytes as BytesValidator,
  Long as LongValidator,
  Typed as TypedValidator,
  As as AsValidator,
  caseInsensitive as caseInsensitiveValidator,
  FiniteDomain,
} from '@janus-validator/core';

// ============================================================================
// Auto-wrapping utilities
// ============================================================================

/**
 * Primitive types that can be automatically wrapped in Constant validators
 */
type Primitive = string | number | boolean;

/**
 * Input that can be either a Validator or a primitive (auto-wrapped in Constant)
 */
export type ValidatorOrPrimitive<T> = Validator<T, Domain<T>> | T;

/**
 * Infer the type from a ValidatorOrPrimitive
 */
type InferType<T> = T extends Validator<infer U, Domain<infer U>> ? U : T;

/**
 * Infer union type from array of ValidatorOrPrimitive
 */
type UnionOfInputs<Ts extends readonly (Validator<any, Domain<any>> | Primitive)[]> = InferType<Ts[number]>;

/**
 * Infer tuple type from array of ValidatorOrPrimitive
 */
type TupleOfInputs<Ts extends readonly (Validator<any, Domain<any>> | Primitive)[]> = {
  [K in keyof Ts]: InferType<Ts[K]>;
};

/**
 * Enum object type (runtime representation of TypeScript enum)
 */
type EnumObject = Record<string, string | number>;

/**
 * Schema where values can be validators, primitives, or enums
 */
type SchemaInput = { [key: string]: Validator<any, Domain<any>> | Primitive | EnumObject };

/**
 * Infer the validated type from a schema value
 */
type InferSchemaValue<T> = 
  T extends Validator<infer U, Domain<infer U>> ? U :
  T extends Record<string, string | number> ? T[keyof T] :  // Enum: extract value types
  T;  // Primitive

/**
 * Infer object type from schema with auto-wrapped primitives and enums
 */
type InferSchemaInput<S extends SchemaInput> = {
  [K in keyof S]: InferSchemaValue<S[K]>;
};

/**
 * Check if an object looks like a TypeScript enum.
 * Enums are plain objects where all values are strings or numbers.
 */
function isEnumObject(obj: unknown): obj is Record<string, string | number> {
  if (obj === null || typeof obj !== 'object' || Array.isArray(obj)) {
    return false;
  }
  const values = Object.values(obj as Record<string, unknown>);
  if (values.length === 0) {
    return false;
  }
  return values.every(v => typeof v === 'string' || typeof v === 'number');
}

/**
 * Internal utility to convert a primitive, enum, or validator to a validator.
 * - Validators pass through unchanged
 * - Primitives are wrapped in Constant
 * - Enum objects are wrapped in Enum (Or of all values)
 * 
 * Used internally by O(), Or(), and Seq() to auto-wrap values.
 */
function v<T>(input: Validator<T, Domain<T>> | T | Record<string, T>): Validator<T, Domain<T>> {
  // Check if it's already a validator
  if (input !== null && typeof input === 'object' && 'validate' in input && 'domain' in input) {
    return input as Validator<T, Domain<T>>;
  }
  // Check if it's an enum object
  if (isEnumObject(input)) {
    // Extract enum values, filtering out reverse mappings from numeric enums
    const values = Object.entries(input)
      .filter(([key]) => isNaN(Number(key)))
      .map(([, value]) => value);
    
    if (values.length > 0) {
      const validators = values.map(val => ConstantValidator(val));
      return AlternationValidator.of(...validators) as unknown as Validator<T, Domain<T>>;
    }
  }
  // Otherwise wrap as constant
  return ConstantValidator(input as T) as unknown as Validator<T, Domain<T>>;
}

// ============================================================================
// Primitive Validators
// ============================================================================

/**
 * Boolean validator
 * @example B()
 */
export const B = (): Validator<boolean, FiniteDomain<boolean>> => BooleanValidator();

/**
 * U - UnicodeString validator for simple strings with length constraints
 * @example U(), U(1, 100)
 */
export const U = (minLength?: number, maxLength?: number): Validator<string, Domain<string>> =>
  UnicodeStringValidator(minLength, maxLength);

// ============================================================================
// Compound String (S)
// ============================================================================

/**
 * S - Builds a formatted string from component parts.
 * 
 * Parts can be literal strings or character set validators.
 * 
 * @example
 * ```typescript
 * // Date: YYYY-MM-DD
 * const date = S(digits(4), '-', digits(2), '-', digits(2));
 * // Or with short alias: S(D(4), '-', D(2), '-', D(2))
 * 
 * // Phone: (XXX) XXX-XXXX
 * const phone = S('(', digits(3), ') ', digits(3), '-', digits(4));
 * 
 * // UUID
 * const uuid = S(hex(8), '-', hex(4), '-', hex(4), '-', hex(4), '-', hex(12));
 * // Or with short alias: S(H(8), '-', H(4), '-', H(4), '-', H(4), '-', H(12))
 * ```
 */
export const S = (...parts: Parameters<typeof CompoundStringValidator>): Validator<string, Domain<string>> =>
  CompoundStringValidator(...parts);

// ============================================================================
// Character Set Validators
// ============================================================================

/** Digits (0-9) */
export const digits = digitsValidator;
/** Digits (0-9) - short alias */
export const D = digitsValidator;

/** Lowercase letters (a-z) */
export const lower = lowerValidator;

/** Uppercase letters (A-Z) */
export const upper = upperValidator;

/** Letters (a-zA-Z) */
export const letters = lettersValidator;

/** Alphanumeric (a-zA-Z0-9) */
export const alphanumeric = alphanumericValidator;
/** Alphanumeric (a-zA-Z0-9) - short alias */
export const A = alphanumericValidator;

/** Hex (0-9a-f) */
export const hex = hexValidator;
/** Hex (0-9a-f) - short alias */
export const H = hexValidator;

/** Uppercase Hex (0-9A-F) */
export const hexUpper = hexUpperValidator;

/** Custom character set */
export const chars = charsValidator;

/**
 * Integer validator
 * @param min Minimum value (default: MIN_SAFE_INTEGER)
 * @param max Maximum value (default: MAX_SAFE_INTEGER)
 * @example I(), I(0, 100)
 */
export const I = (min?: number, max?: number): Validator<number, Domain<number>> =>
  IntegerValidator(min, max);

/**
 * Number (float) validator
 * @param min Minimum value (default: -MAX_VALUE)
 * @param max Maximum value (default: MAX_VALUE)
 * @example N(), N(0, 1)
 */
export const N = (min?: number, max?: number): Validator<number, Domain<number>> =>
  FloatValidator(min, max);

/**
 * Long (bigint) validator - for 64-bit integers
 * @param min Minimum value (default: -2^63)
 * @param max Maximum value (default: 2^63-1)
 * @example L(), L(0n, 1000000000000n)
 */
export const L = (min?: bigint, max?: bigint): Validator<bigint, Domain<bigint>> =>
  LongValidator(min, max);

/**
 * Bytes (binary) validator
 * @param minLength Minimum byte length (default: 0)
 * @param maxLength Maximum byte length (default: 1024)
 * @example Bytes(), Bytes(16, 16) // fixed 16 bytes
 */
export const Bytes = (minLength?: number, maxLength?: number): Validator<Uint8Array, Domain<Uint8Array>> =>
  BytesValidator(minLength, maxLength);

/**
 * Regex validator
 * @param pattern Regular expression pattern
 * @example R(/^hello$/), R(/\d{3}-\d{4}/)
 */
export const R = (pattern: RegExp): Validator<string, Domain<string>> =>
  RegexValidator(pattern);

/**
 * Struct (object) validator.
 * Primitives in the schema are automatically wrapped in Constant.
 * @param schema Object mapping property names to validators or primitives
 * @param strict If true, reject objects with extra properties
 * @example
 * ```typescript
 * // Primitives auto-wrapped
 * const config = O({
 *   version: 1,
 *   env: 'production',
 *   port: I(1, 65535),
 * });
 * ```
 */
export const O = <T extends SchemaInput>(
  schema: T,
  strict: boolean = false
): Validator<InferSchemaInput<T>, Domain<InferSchemaInput<T>>> => {
  const wrappedSchema: StructSchema = {};
  for (const [key, value] of Object.entries(schema)) {
    wrappedSchema[key] = v(value);
  }
  return StructValidator(wrappedSchema, strict) as Validator<InferSchemaInput<T>, Domain<InferSchemaInput<T>>>;
};

/**
 * Constant validator - validates a single exact value
 * @param value The exact value to validate
 * @param comparator Optional custom comparison function
 * @param displayName Optional name for error messages
 * @example C(42), C('hello')
 */
export const C = <T>(
  value: T,
  comparator?: (input: unknown, value: T) => boolean,
  displayName?: string
): Validator<T, Domain<T>> =>
  ConstantValidator(value, comparator, displayName);

// ============================================================================
// Special Values
// ============================================================================

/**
 * Null validator
 * @example Null()
 */
export { NullValidator as Null };

/**
 * Undefined validator
 * @example Undefined()
 */
export { UndefinedValidator as Undefined };

/**
 * Positive Infinity validator
 * @example Inf()
 */
export const Inf = (): Validator<number, Domain<number>> => InfinityValidator();

/**
 * Negative Infinity validator
 * @example NInf()
 */
export const NInf = (): Validator<number, Domain<number>> => NegativeInfinityValidator();

/**
 * NaN validator
 * @example NaN()
 */
export { NaNValidator as NaN };

// ============================================================================
// Combinators
// ============================================================================

/**
 * Or (Alternation) - validates if any one of the validators matches.
 * Primitives (string, number, boolean) are automatically wrapped in Constant.
 * Type is automatically inferred as union of all types.
 * @param inputs List of validators or primitives to try
 * @example
 * ```typescript
 * // Type is Validator<string | number | null>
 * const v = Or(U(), I(), Null());
 * 
 * // Primitives are auto-wrapped in Constant
 * const protocol = Or('http', 'https', 'ws', 'wss');
 * const status = Or(200, 201, 204, 404, 500);
 * ```
 */
export const Or = <Vs extends readonly (Validator<any, Domain<any>> | Primitive)[]>(
  ...inputs: Vs
): Validator<UnionOfInputs<Vs>, Domain<UnionOfInputs<Vs>>> => {
  const validators = inputs.map(input => v(input));
  return AlternationValidator.of(...validators) as Validator<UnionOfInputs<Vs>, Domain<UnionOfInputs<Vs>>>;
};

/**
 * Enum - creates a validator from a TypeScript enum.
 * Extracts enum values and creates an Or validator with each value as a Constant.
 * Works with both string and numeric enums.
 * 
 * @param enumObj The TypeScript enum object
 * @example
 * ```typescript
 * enum Status {
 *   Pending = 'pending',
 *   Active = 'active',
 *   Completed = 'completed',
 * }
 * 
 * const statusValidator = Enum(Status);
 * // Equivalent to: Or('pending', 'active', 'completed')
 * 
 * statusValidator.validate('pending');  // ✓
 * statusValidator.validate('invalid');  // ✗
 * 
 * // Works with numeric enums too
 * enum Direction { Up, Down, Left, Right }
 * const dirValidator = Enum(Direction);  // Or(0, 1, 2, 3)
 * ```
 */
export const Enum = <T extends string | number>(
  enumObj: Record<string, T>
): Validator<T, Domain<T>> => {
  // Extract enum values, filtering out reverse mappings from numeric enums
  const values = Object.entries(enumObj)
    .filter(([key]) => isNaN(Number(key))) // Filter out numeric keys (reverse mappings)
    .map(([, value]) => value);
  
  if (values.length === 0) {
    throw new Error('Enum must have at least one value');
  }
  
  const validators = values.map(val => ConstantValidator(val));
  return AlternationValidator.of(...validators) as Validator<T, Domain<T>>;
};

/**
 * Sequence - validates a tuple where each element matches its corresponding validator.
 * Primitives are automatically wrapped in Constant.
 * Type is automatically inferred as a tuple.
 * @param inputs List of validators or primitives for each position
 * @example
 * ```typescript
 * // Type is Validator<[string, number, boolean]>
 * const point = Seq(U(), I(), B());
 * 
 * // Primitives auto-wrapped
 * const header = Seq('v1', I(), 'end');
 * // Type: Validator<['v1', number, 'end']>
 * ```
 */
export const Seq = <Vs extends readonly (Validator<any, Domain<any>> | Primitive)[]>(
  ...inputs: Vs
): Validator<TupleOfInputs<Vs>, Domain<TupleOfInputs<Vs>>> => {
  const validators = inputs.map(input => v(input));
  return SequenceValidator.of(...validators) as Validator<TupleOfInputs<Vs>, Domain<TupleOfInputs<Vs>>>;
};

// ============================================================================
// Quantifier Functions
// ============================================================================

/**
 * Zero or more - validates arrays of any length (including empty)
 * @param validator Validator for each element
 * @example zeroOrMore(S())
 */
export const zeroOrMore = <T, D extends Domain<T>>(validator: Validator<T, D>): Validator<T[], Domain<T[]>> =>
  QuantifierValidator.zeroOrMore(validator);

/**
 * One or more - validates arrays with at least one element
 * @param validator Validator for each element
 * @example oneOrMore(I(0, 100))
 */
export const oneOrMore = <T, D extends Domain<T>>(validator: Validator<T, D>): Validator<T[], Domain<T[]>> =>
  QuantifierValidator.oneOrMore(validator);

/**
 * Optional - validates arrays with 0 or 1 element
 * @param validator Validator for the optional element
 * @example optional(S())
 */
export const optional = <T, D extends Domain<T>>(validator: Validator<T, D>): Validator<T[], Domain<T[]>> =>
  QuantifierValidator.optional(validator);

/**
 * Exactly N - validates arrays with exactly n elements
 * @param validator Validator for each element
 * @param n Exact number of elements required
 * @example exactly(I(), 3)
 */
export const exactly = <T, D extends Domain<T>>(validator: Validator<T, D>, n: number): Validator<T[], Domain<T[]>> =>
  QuantifierValidator.exactly(validator, n);

/**
 * At least N - validates arrays with n or more elements
 * @param validator Validator for each element
 * @param n Minimum number of elements
 * @example atLeast(S(), 2)
 */
export const atLeast = <T, D extends Domain<T>>(validator: Validator<T, D>, n: number): Validator<T[], Domain<T[]>> =>
  QuantifierValidator.atLeast(validator, n);

/**
 * Between min and max - validates arrays with length in range
 * @param validator Validator for each element
 * @param min Minimum number of elements
 * @param max Maximum number of elements
 * @example between(I(), 1, 5)
 */
export const between = <T, D extends Domain<T>>(validator: Validator<T, D>, min: number, max: number): Validator<T[], Domain<T[]>> =>
  QuantifierValidator.between(validator, min, max);

// ============================================================================
// Type Assertion Helpers
// ============================================================================

/**
 * Force a validator's output type to match your interface.
 * Provides compile-time checking that the validator matches the target type.
 * 
 * @example
 * ```typescript
 * interface User {
 *   name: string;
 *   age: number;
 * }
 * 
 * const userValidator = Typed<User>()(O({
 *   name: U(),
 *   age: I(),
 * }));
 * 
 * const result = userValidator.validate(input);
 * if (result.valid) {
 *   result.value; // Typed as User directly!
 * }
 * ```
 */
export const Typed = TypedValidator;

/**
 * Alias for Typed - assert output type matches interface
 * @example As<User>()(O({ name: U(), age: I() }))
 */
export const As = AsValidator;

// ============================================================================
// String Modifiers
// ============================================================================

/**
 * Makes a string validator case-insensitive by normalizing input to lowercase.
 * The original value (with original casing) is preserved in the result.
 * 
 * @param validator The string validator to make case-insensitive
 * @example
 * ```typescript
 * const hexColor = caseInsensitive(S('#', hex(6)));
 * hexColor.validate('#aabbcc'); // valid
 * hexColor.validate('#AABBCC'); // valid
 * hexColor.validate('#AaBbCc'); // valid
 * ```
 */
export const caseInsensitive = caseInsensitiveValidator;

// ============================================================================
// Value Modifiers (Nullable, Nullish, Default)
// ============================================================================
// 
// Note: For making a value accept `undefined`, use the fluent method `.optional()`:
//   const maybeName = U(1, 50).optional();  // string | undefined
// 
// The standalone `optional()` function in this DSL is for array quantifiers (0 or 1 elements).
// This follows the established naming convention in the DSL.

// Import and re-export modifier functions
import {
  nullable as nullableModifier,
  nullish as nullishModifier,
  withDefault as withDefaultFn,
  transform as transformFn,
} from '@janus-validator/core';

/**
 * Makes a validator accept null in addition to its normal type.
 * 
 * @param validator The validator to wrap
 * @returns A new validator that accepts T | null
 * 
 * @example
 * ```typescript
 * const nullableName = nullable(U(1, 50));
 * nullableName.validate("Alice");  // valid
 * nullableName.validate(null);     // valid
 * 
 * // Or use the fluent method:
 * const nullableName = U(1, 50).nullable();
 * ```
 */
export const nullable = nullableModifier;

/**
 * Makes a validator accept null or undefined in addition to its normal type.
 * 
 * @param validator The validator to wrap
 * @returns A new validator that accepts T | null | undefined
 * 
 * @example
 * ```typescript
 * const nullishName = nullish(U(1, 50));
 * nullishName.validate("Alice");    // valid
 * nullishName.validate(null);       // valid
 * nullishName.validate(undefined);  // valid
 * 
 * // Or use the fluent method:
 * const nullishName = U(1, 50).nullish();
 * ```
 */
export const nullish = nullishModifier;

/**
 * Provides a default value when input is undefined.
 * 
 * @param validator The validator to wrap
 * @param value Default value (static) or factory function (dynamic)
 * @returns A new validator that uses the default for undefined inputs
 * 
 * @example
 * ```typescript
 * // Static default
 * const port = withDefault(I(1, 65535), 3000);
 * port.validate(8080);      // { valid: true, value: 8080 }
 * port.validate(undefined); // { valid: true, value: 3000 }
 * 
 * // Dynamic default
 * const timestamp = withDefault(I(), () => Date.now());
 * 
 * // Or use the fluent method:
 * const port = I(1, 65535).default(3000);
 * ```
 */
export const withDefault = withDefaultFn;

/**
 * Transforms the validated value using the provided function.
 * 
 * The transform is applied after successful validation. If the transform
 * throws an error, it becomes a validation error.
 * 
 * @param validator The validator to wrap
 * @param fn The transformation function
 * @param errorMessage Optional custom error message for transform failures
 * @returns A new validator that produces transformed values
 * 
 * @example
 * ```typescript
 * // Basic transform
 * const trimmed = transform(U(1, 100), s => s.trim());
 * trimmed.validate("  hello  "); // { valid: true, value: "hello" }
 * 
 * // Type-changing transform (string to number)
 * const toInt = transform(U(), s => parseInt(s, 10));
 * toInt.validate("42"); // { valid: true, value: 42 }
 * 
 * // Or use the fluent method:
 * const trimmed = U(1, 100).trim();
 * const lower = U().toLowerCase();
 * const chained = U().transform(s => s.trim()).transform(s => s.toLowerCase());
 * ```
 */
export { transformFn as transform };

// ============================================================================
// Refinements
// ============================================================================

import {
  refine as refineFn,
  superRefine as superRefineFn,
} from '@janus-validator/core';

/**
 * Adds a custom validation predicate to a validator.
 * 
 * The refinement runs after the inner validator succeeds.
 * **Note:** Refinements do NOT affect the domain - generated values may fail refinement.
 * 
 * @param validator The validator to wrap
 * @param predicate Function returning true if valid
 * @param message Error message (string or function)
 * @returns A new validator with the additional check
 * 
 * @example
 * ```typescript
 * // Simple predicate
 * const even = refine(I(0, 100), n => n % 2 === 0, 'Must be even');
 * 
 * // Dynamic message
 * const positive = refine(N(), n => n > 0, n => `Expected positive, got ${n}`);
 * 
 * // Or use the fluent method:
 * const even = I(0, 100).refine(n => n % 2 === 0, 'Must be even');
 * const positiveInt = I().positive();
 * const validEmail = U(5, 100).email();
 * ```
 */
export const refine = refineFn;

/**
 * Adds complex validation with multiple potential issues.
 * 
 * Use this when you need to report multiple validation issues at once
 * or when validation logic is complex.
 * 
 * @param validator The validator to wrap
 * @param refinement Function that calls ctx.addIssue() for problems
 * @returns A new validator that collects all issues
 * 
 * @example
 * ```typescript
 * // Password strength validation
 * const password = superRefine(U(8, 100), (value, ctx) => {
 *   if (!/[A-Z]/.test(value)) ctx.addIssue({ message: 'Need uppercase' });
 *   if (!/[0-9]/.test(value)) ctx.addIssue({ message: 'Need digit' });
 * });
 * 
 * // Cross-field validation
 * const registration = superRefine(
 *   O({ password: U(8, 100), confirm: U(8, 100) }),
 *   (value, ctx) => {
 *     if (value.password !== value.confirm) {
 *       ctx.addIssue({ message: 'Passwords must match', path: ['confirm'] });
 *     }
 *   }
 * );
 * 
 * // Or use the fluent method:
 * const password = U(8, 100).superRefine((s, ctx) => { ... });
 * ```
 */
export const superRefine = superRefineFn;

// ============================================================================
// Error Customization
// ============================================================================

import {
  message as messageFn,
  code as codeFn,
  describe as describeFn,
} from '@janus-validator/core';

/**
 * Override the error message for a validator.
 * 
 * @param validator The validator to wrap
 * @param msg Static message or function (originalError, value) => message
 * @returns A new validator with the custom message
 * 
 * @example
 * ```typescript
 * const age = message(I(0, 150), 'Please enter a valid age');
 * 
 * const count = message(I(1, 100), (err, val) => 
 *   `Invalid count "${val}": ${err}`
 * );
 * 
 * // Or use the fluent method:
 * const age = I(0, 150).message('Please enter a valid age');
 * ```
 */
export const message = messageFn;

/**
 * Add an error code for i18n or programmatic handling.
 * 
 * @param validator The validator to wrap
 * @param errorCode The error code to attach
 * @returns A new validator with the error code
 * 
 * @example
 * ```typescript
 * const email = code(
 *   U(5, 100).refine(s => s.includes('@')),
 *   'INVALID_EMAIL'
 * );
 * 
 * // Or use the fluent method:
 * const email = U(5, 100).refine(s => s.includes('@')).code('INVALID_EMAIL');
 * ```
 */
export const code = codeFn;

/**
 * Add a description for documentation.
 * 
 * @param validator The validator to wrap
 * @param description Human-readable description
 * @returns A new validator with the description
 * 
 * @example
 * ```typescript
 * const email = describe(U(5, 100), 'User email for account recovery');
 * 
 * // Or use the fluent method:
 * const email = U(5, 100).describe('User email for account recovery');
 * ```
 */
export const describe = describeFn;

// ============================================================================
// Error Formatting Utilities
// ============================================================================

export {
  flattenErrors,
  formatErrors,
  errorsToJson,
  getFirstError,
  getErrorAtPath,
  getErrorsByPath,
  type FormattedError,
} from '@janus-validator/core';

// ============================================================================
// Lib Validators (Re-exports from @janus-validator/lib)
// ============================================================================

// Network
export {
  URL,
  SimpleURL,
  SecureURL,
  WebSocketURL,
  FTPURL,
  Domain,
  Subdomain,
  Hostname,
  IPv4,
  IPv4Simple,
  IPv6,
  IPv6Full,
  IPAddress,
  CIDR,
  PrivateIPv4,
  Port,
  WellKnownPort,
  RegisteredPort,
  DynamicPort,
  MACAddressColon,
  MACAddressHyphen,
  MACAddress,
  HostPort,
  ServerConfig,
} from '@janus-validator/lib';

// Identifiers
export {
  UUID,
  UUIDv4,
  UUIDNoDashes,
  UUIDSimple,
  Slug,
  Base64ID,
  NanoID,
  ShortID,
  IntegerID,
  ObjectID,
  SnowflakeID,
  CUID,
  ULID,
  SemVer,
  SemVerFull,
  MD5Hash,
  SHA1Hash,
  SHA256Hash,
  GitCommitHash,
  HexColor,
  HexColor3,
  HexColor4,
  HexColor6,
  HexColor8,
  HexColorAlpha,
  LanguageCode,
  LocaleCode,
  WithID,
  WithTimestamps,
} from '@janus-validator/lib';

// Contact
export {
  Email,
  StrictEmail,
  CorporateEmail,
  USPhoneFormatted,
  USPhone,
  InternationalPhone,
  E164Phone,
  UKPhone,
  TwitterHandle,
  InstagramHandle,
  LinkedInURL,
  ContactForm,
  FullContact,
} from '@janus-validator/lib';

// Credentials
export {
  Username,
  UsernameWithDots,
  Handle,
  Password,
  PIN,
  PIN4,
  PIN6,
  JWT,
  APIKey,
  BearerToken,
} from '@janus-validator/lib';

// DateTime
export {
  ISODate,
  ISODateTime,
  USDate,
  EUDate,
  Year,
  Month,
  DayOfMonth,
  Time24,
  Time24WithSeconds,
  Time12,
  Hour24,
  Hour12,
  Minute,
  Second,
  IANATimezone,
  UTCOffset,
  ISODuration,
  DurationMs,
  DurationSeconds,
  DateRange,
  DateTimeRange,
  ScheduledEvent,
  CronExpression,
} from '@janus-validator/lib';

// Financial
export {
  CreditCardNumber,
  VisaCard,
  MasterCard,
  AmexCard,
  CVV,
  CardExpiryShort,
  CardExpiryLong,
  CardExpiry,
  CreditCard,
  CurrencyCode,
  MoneyAmount,
  Price,
  Percentage,
  Money,
  USRoutingNumber,
  USBankAccountNumber,
  IBAN,
  SWIFT,
  USBankAccount,
  SSNFormatted,
  SSN,
  EINFormatted,
  EIN,
  UKVAT,
  EUVAT,
  Transaction,
  PaymentMethod,
} from '@janus-validator/lib';

// Location
export {
  USZip5,
  USZipPlus4,
  USZipCode,
  UKPostcode,
  CanadianPostalCode,
  GermanPLZ,
  PostalCode,
  Latitude,
  Longitude,
  Coordinates,
  Coordinates3D,
  CountryCodeAlpha2,
  CountryCodeAlpha3,
  USStateCode,
  USAddress,
  UKAddress,
  InternationalAddress,
  ShippingAddress,
  GeoLocation,
} from '@janus-validator/lib';

// Realistic Presets
export {
  FirstName,
  LastName,
  FullName,
  RealisticUsername,
  RealisticEmail,
  CorporateEmailPreset,
  RealisticStreetAddress,
  RealisticCity,
  RealisticState,
  RealisticZipCode,
  RealisticUSPhone,
  CompanyName,
  ProductName,
  LoremIpsum,
  RecentDate,
  FutureDate,
  RealisticPrice,
} from '@janus-validator/lib';