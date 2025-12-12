/**
 * Type utilities for Janus validators and domains
 * 
 * These helper types enable automatic type inference for combinators and domains.
 */

import { Validator } from './Validator';
import type { Domain } from './Domain';

// ============================================================================
// Core Type Extraction - Validators
// ============================================================================

/**
 * Extract the value type T from a Validator<T>
 * 
 * @example
 * type S = InferValidatorType<Validator<string>>; // string
 */
export type InferValidatorType<V> = V extends Validator<infer T> ? T : never;

// ============================================================================
// Core Type Extraction - Domains
// ============================================================================

/**
 * Extract the value type T from a Domain<T>
 * 
 * @example
 * type S = InferDomainType<Domain<string>>; // string
 */
export type InferDomainType<D> = D extends Domain<infer T> ? T : never;

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

/**
 * Extract union type from a tuple/array of domains
 * 
 * @example
 * type U = UnionOfDomains<[Domain<string>, Domain<number>]>; // string | number
 */
export type UnionOfDomains<Ds extends readonly Domain<any>[]> = 
  InferDomainType<Ds[number]>;

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

/**
 * Map a tuple of domains to a tuple of their value types
 * 
 * @example
 * type T = TupleOfDomains<[Domain<string>, Domain<number>]>; // [string, number]
 */
export type TupleOfDomains<Ds extends readonly Domain<any>[]> = {
  [K in keyof Ds]: InferDomainType<Ds[K]>;
};

/**
 * Map a tuple of value types to a tuple of domains for those types
 * (inverse of TupleOfDomains)
 * 
 * @example
 * type Parts = DomainsForTuple<[string, number]>; // [Domain<string>, Domain<number>]
 */
export type DomainsForTuple<T extends readonly unknown[]> = {
  [K in keyof T]: Domain<T[K]>;
};

// ============================================================================
// Object Types (for Struct / O)
// ============================================================================

/**
 * Schema definition for Struct validator - maps property names to validators
 */
export type ValidatorSchema = {
  [key: string]: Validator<unknown>;
};

/**
 * Schema definition for Struct domain - maps property names to domains
 */
export type DomainSchema = {
  [key: string]: Domain<unknown>;
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

/**
 * Infer the object type from a domain schema
 * 
 * @example
 * type U = InferDomainSchemaType<{ name: Domain<string>, age: Domain<number> }>;
 * // { name: string; age: number }
 */
export type InferDomainSchemaType<S extends DomainSchema> = {
  [K in keyof S]: InferDomainType<S[K]>;
};

/**
 * Map an object type to a schema of domains for each property
 * (inverse of InferDomainSchemaType)
 * 
 * @example
 * type S = DomainsForObject<{ name: string, age: number }>;
 * // { name: Domain<string>; age: Domain<number> }
 */
export type DomainsForObject<T> = {
  [K in keyof T]: Domain<T[K]>;
};
