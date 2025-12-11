/**
 * Type utilities for Janus validators
 * 
 * These helper types enable automatic type inference for combinators.
 */

import { Validator } from './Validator';

// ============================================================================
// Core Type Extraction
// ============================================================================

/**
 * Extract the value type T from a Validator<T>
 * 
 * @example
 * type S = InferValidatorType<Validator<string>>; // string
 */
export type InferValidatorType<V> = V extends Validator<infer T> ? T : never;

// ============================================================================
// Union Types (for Alternation / Or)
// ============================================================================

/**
 * Extract union type from a tuple/array of validators
 * 
 * @example
 * type U = UnionOfValidators<[Validator<string>, Validator<number>]>; // string | number
 */
export type UnionOfValidators<Vs extends readonly Validator<any>[]> = 
  InferValidatorType<Vs[number]>;

// ============================================================================
// Tuple Types (for Sequence / Seq)
// ============================================================================

/**
 * Map a tuple of validators to a tuple of their value types
 * 
 * @example
 * type T = TupleOfValidators<[Validator<string>, Validator<number>]>; // [string, number]
 */
export type TupleOfValidators<Vs extends readonly Validator<any>[]> = {
  [K in keyof Vs]: InferValidatorType<Vs[K]>;
};

// ============================================================================
// Object Types (for Struct / O)
// ============================================================================

/**
 * Schema definition for Struct validator - maps property names to validators
 */
export type ValidatorSchema = {
  [key: string]: Validator<any>;
};

/**
 * Infer the object type from a validator schema
 * 
 * @example
 * type U = InferSchemaType<{ name: Validator<string>, age: Validator<number> }>;
 * // { name: string; age: number }
 */
export type InferSchemaType<S extends ValidatorSchema> = {
  [K in keyof S]: InferValidatorType<S[K]>;
};

