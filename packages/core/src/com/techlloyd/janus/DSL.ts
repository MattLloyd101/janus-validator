/**
 * DSL - Short aliases for all combinators
 * 
 * All validators are automatically wrapped with withExample() so validation
 * errors always include a valid example.
 * 
 * @example
 * ```typescript
 * import { B, S, I, N, L, R, O, Bytes, Or, Seq, optional, oneOrMore } from './DSL';
 * 
 * // Simple validators
 * const isBoolean = B();
 * const isString = S(1, 100);
 * const isInteger = I(0, 100);
 * const isLong = L();  // 64-bit bigint
 * const isBinary = Bytes(0, 1024);
 * 
 * // Object schema
 * const user = O({
 *   name: S(1, 50),
 *   age: I(0, 150),
 *   active: B()
 * });
 * 
 * // Regex
 * const email = R(/^[\w.]+@[\w.]+\.\w+$/);
 * 
 * // Combinators
 * const stringOrNumber = Or(S(), N());
 * const tags = oneOrMore(S(1, 20));
 * ```
 */

import { Validator } from './Validator';
import { withExample } from './combinators/WithExample';
import { Boolean as BooleanValidator } from './combinators/Boolean';
import { UnicodeString as UnicodeStringValidator } from './combinators/UnicodeString';
import {
  String as StringValidator,
  digits as digitsValidator,
  lower as lowerValidator,
  upper as upperValidator,
  letters as lettersValidator,
  alphanumeric as alphanumericValidator,
  hex as hexValidator,
  hexUpper as hexUpperValidator,
  chars as charsValidator,
} from './combinators/String';
import { Integer as IntegerValidator } from './combinators/Integer';
import { Number as NumberValidator } from './combinators/Number';
import { Regex as RegexValidator } from './combinators/Regex';
import { Struct as StructValidator, StructSchema } from './combinators/Struct';
import { Constant as ConstantValidator } from './combinators/Constant';
import { Alternation as AlternationValidator } from './combinators/Alternation';
import { Sequence as SequenceValidator } from './combinators/Sequence';
import { Quantifier as QuantifierValidator } from './combinators/Quantifier';
import { Null as NullValidator } from './combinators/Null';
import { Undefined as UndefinedValidator } from './combinators/Undefined';
import { Infinity as InfinityValidator, NegativeInfinity as NegativeInfinityValidator } from './combinators/Infinity';
import { NaN as NaNValidator } from './combinators/NaN';
import { Bytes as BytesValidator } from './combinators/Bytes';
import { Long as LongValidator } from './combinators/Long';
import { createCaptureGroup as createCaptureGroupBase, ValidationContext } from './combinators/Capture';
import { Typed as TypedValidator, As as AsValidator } from './combinators/Typed';
import { caseInsensitive as caseInsensitiveValidator } from './combinators/CaseInsensitive';

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
export type ValidatorOrPrimitive<T> = Validator<T> | T;

/**
 * Infer the type from a ValidatorOrPrimitive
 */
type InferType<T> = T extends Validator<infer U> ? U : T;

/**
 * Infer union type from array of ValidatorOrPrimitive
 */
type UnionOfInputs<Ts extends readonly (Validator<any> | Primitive)[]> = InferType<Ts[number]>;

/**
 * Infer tuple type from array of ValidatorOrPrimitive
 */
type TupleOfInputs<Ts extends readonly (Validator<any> | Primitive)[]> = {
  [K in keyof Ts]: InferType<Ts[K]>;
};

/**
 * Enum object type (runtime representation of TypeScript enum)
 */
type EnumObject = Record<string, string | number>;

/**
 * Schema where values can be validators, primitives, or enums
 */
type SchemaInput = { [key: string]: Validator<any> | Primitive | EnumObject };

/**
 * Infer the validated type from a schema value
 */
type InferSchemaValue<T> = 
  T extends Validator<infer U> ? U :
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
function v<T>(input: Validator<T> | T | Record<string, T>): Validator<T> {
  // Check if it's already a validator
  if (input !== null && typeof input === 'object' && 'validate' in input && 'domain' in input) {
    return input as Validator<T>;
  }
  // Check if it's an enum object
  if (isEnumObject(input)) {
    // Extract enum values, filtering out reverse mappings from numeric enums
    const values = Object.entries(input)
      .filter(([key]) => isNaN(Number(key)))
      .map(([, value]) => value);
    
    if (values.length > 0) {
      const validators = values.map(val => ConstantValidator(val));
      return withExample(AlternationValidator.of(...validators)) as Validator<T>;
    }
  }
  // Otherwise wrap as constant
  return ConstantValidator(input as T) as Validator<T>;
}

// ============================================================================
// Primitive Validators
// ============================================================================

/**
 * Boolean validator
 * @example B()
 */
export const B = (): Validator<boolean> => withExample(BooleanValidator());

/**
 * U - UnicodeString validator for simple strings with length constraints
 * @example U(), U(1, 100)
 */
export const U = (minLength?: number, maxLength?: number): Validator<string> =>
  withExample(UnicodeStringValidator(minLength, maxLength));

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
export const S = (...parts: Parameters<typeof StringValidator>): Validator<string> =>
  withExample(StringValidator(...parts));

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
export const I = (min?: number, max?: number): Validator<number> =>
  withExample(IntegerValidator(min, max));

/**
 * Number (float) validator
 * @param min Minimum value (default: -MAX_VALUE)
 * @param max Maximum value (default: MAX_VALUE)
 * @example N(), N(0, 1)
 */
export const N = (min?: number, max?: number): Validator<number> =>
  withExample(NumberValidator(min, max));

/**
 * Long (bigint) validator - for 64-bit integers
 * @param min Minimum value (default: -2^63)
 * @param max Maximum value (default: 2^63-1)
 * @example L(), L(0n, 1000000000000n)
 */
export const L = (min?: bigint, max?: bigint): Validator<bigint> =>
  withExample(LongValidator(min, max));

/**
 * Bytes (binary) validator
 * @param minLength Minimum byte length (default: 0)
 * @param maxLength Maximum byte length (default: 1024)
 * @example Bytes(), Bytes(16, 16) // fixed 16 bytes
 */
export const Bytes = (minLength?: number, maxLength?: number): Validator<Uint8Array> =>
  withExample(BytesValidator(minLength, maxLength));

/**
 * Regex validator
 * @param pattern Regular expression pattern
 * @example R(/^hello$/), R(/\d{3}-\d{4}/)
 */
export const R = (pattern: RegExp): Validator<string> =>
  withExample(RegexValidator(pattern));

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
): Validator<InferSchemaInput<T>> => {
  const wrappedSchema: StructSchema = {};
  for (const [key, value] of Object.entries(schema)) {
    wrappedSchema[key] = v(value);
  }
  return withExample(StructValidator(wrappedSchema, strict)) as Validator<InferSchemaInput<T>>;
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
): Validator<T> =>
  withExample(ConstantValidator(value, comparator, displayName));

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
export const Inf = (): Validator<number> => withExample(InfinityValidator());

/**
 * Negative Infinity validator
 * @example NInf()
 */
export const NInf = (): Validator<number> => withExample(NegativeInfinityValidator());

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
 * const v = Or(S(), I(), Null());
 * 
 * // Primitives are auto-wrapped in Constant
 * const protocol = Or('http', 'https', 'ws', 'wss');
 * const status = Or(200, 201, 204, 404, 500);
 * ```
 */
export const Or = <Vs extends readonly (Validator<any> | Primitive)[]>(
  ...inputs: Vs
): Validator<UnionOfInputs<Vs>> => {
  const validators = inputs.map(input => v(input));
  return withExample(AlternationValidator.of(...validators)) as Validator<UnionOfInputs<Vs>>;
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
): Validator<T> => {
  // Extract enum values, filtering out reverse mappings from numeric enums
  const values = Object.entries(enumObj)
    .filter(([key]) => isNaN(Number(key))) // Filter out numeric keys (reverse mappings)
    .map(([, value]) => value);
  
  if (values.length === 0) {
    throw new Error('Enum must have at least one value');
  }
  
  const validators = values.map(val => ConstantValidator(val));
  return withExample(AlternationValidator.of(...validators)) as Validator<T>;
};

/**
 * Sequence - validates a tuple where each element matches its corresponding validator.
 * Primitives are automatically wrapped in Constant.
 * Type is automatically inferred as a tuple.
 * @param inputs List of validators or primitives for each position
 * @example
 * ```typescript
 * // Type is Validator<[string, number, boolean]>
 * const point = Seq(S(), I(), B());
 * 
 * // Primitives auto-wrapped
 * const header = Seq('v1', I(), 'end');
 * // Type: Validator<['v1', number, 'end']>
 * ```
 */
export const Seq = <Vs extends readonly (Validator<any> | Primitive)[]>(
  ...inputs: Vs
): Validator<TupleOfInputs<Vs>> => {
  const validators = inputs.map(input => v(input));
  return withExample(SequenceValidator.of(...validators)) as Validator<TupleOfInputs<Vs>>;
};

// ============================================================================
// Quantifier Functions
// ============================================================================

/**
 * Zero or more - validates arrays of any length (including empty)
 * @param validator Validator for each element
 * @example zeroOrMore(S())
 */
export const zeroOrMore = <T>(validator: Validator<T>): Validator<T[]> =>
  withExample(QuantifierValidator.zeroOrMore(validator));

/**
 * One or more - validates arrays with at least one element
 * @param validator Validator for each element
 * @example oneOrMore(I(0, 100))
 */
export const oneOrMore = <T>(validator: Validator<T>): Validator<T[]> =>
  withExample(QuantifierValidator.oneOrMore(validator));

/**
 * Optional - validates arrays with 0 or 1 element
 * @param validator Validator for the optional element
 * @example optional(S())
 */
export const optional = <T>(validator: Validator<T>): Validator<T[]> =>
  withExample(QuantifierValidator.optional(validator));

/**
 * Exactly N - validates arrays with exactly n elements
 * @param validator Validator for each element
 * @param n Exact number of elements required
 * @example exactly(I(), 3)
 */
export const exactly = <T>(validator: Validator<T>, n: number): Validator<T[]> =>
  withExample(QuantifierValidator.exactly(validator, n));

/**
 * At least N - validates arrays with n or more elements
 * @param validator Validator for each element
 * @param n Minimum number of elements
 * @example atLeast(S(), 2)
 */
export const atLeast = <T>(validator: Validator<T>, n: number): Validator<T[]> =>
  withExample(QuantifierValidator.atLeast(validator, n));

/**
 * Between min and max - validates arrays with length in range
 * @param validator Validator for each element
 * @param min Minimum number of elements
 * @param max Maximum number of elements
 * @example between(I(), 1, 5)
 */
export const between = <T>(validator: Validator<T>, min: number, max: number): Validator<T[]> =>
  withExample(QuantifierValidator.between(validator, min, max));

// ============================================================================
// Capture Group
// ============================================================================

/**
 * Create a capture group for capturing and referencing values during validation
 * Useful for scenarios like password confirmation
 * @example
 * const { capture, ref, context } = createCaptureGroup();
 * const form = O({
 *   password: capture('pwd', S(8, 100)),
 *   confirmPassword: ref('pwd'),
 * });
 */
export const createCaptureGroup = createCaptureGroupBase;
export { ValidationContext };

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
 *   name: S(),
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
 * @example As<User>()(O({ name: S(), age: I() }))
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
