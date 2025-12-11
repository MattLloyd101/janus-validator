import { ContiguousTypeValue } from './domains/interpolate/ContiguousType';

/**
 * Domain type enum
 */
export enum DomainType {
  FINITE_DOMAIN = 'FINITE_DOMAIN',
  STRING_DOMAIN = 'STRING_DOMAIN',
  CONTIGUOUS_DOMAIN = 'CONTIGUOUS_DOMAIN',
  REGEX_DOMAIN = 'REGEX_DOMAIN',
  ALTERNATION_DOMAIN = 'ALTERNATION_DOMAIN',
  SEQUENCE_DOMAIN = 'SEQUENCE_DOMAIN',
  QUANTIFIER_DOMAIN = 'QUANTIFIER_DOMAIN',
  STRUCT_DOMAIN = 'STRUCT_DOMAIN',
  CAPTURE_DOMAIN = 'CAPTURE_DOMAIN',
  REF_DOMAIN = 'REF_DOMAIN',
  CUSTOM_GENERATOR_DOMAIN = 'CUSTOM_GENERATOR_DOMAIN',
  BYTES_DOMAIN = 'BYTES_DOMAIN',
  BIGINT_DOMAIN = 'BIGINT_DOMAIN',
}

/**
 * Domain describes the set of valid values for a validator
 */
// eslint-disable-next-line unused-imports/no-unused-vars
export interface Domain<T> {
  type: DomainType;
}

/**
 * Finite domain for values with a fixed set of possible values
 */
export interface FiniteDomain<T> extends Domain<T> {
  type: DomainType.FINITE_DOMAIN;
  values: readonly T[];
}

/**
 * String domain for valid Unicode strings
 */
export interface StringDomain extends Domain<string> {
  type: DomainType.STRING_DOMAIN;
  minLength?: number;
  maxLength?: number;
}

/**
 * Contiguous domain for numeric ranges (min to max inclusive)
 */
export interface ContiguousDomain extends Domain<number> {
  type: DomainType.CONTIGUOUS_DOMAIN;
  contiguousType: ContiguousTypeValue;
  min: number;
  max: number;
}

/**
 * Regex domain for strings matching a regular expression pattern
 * The pattern is stored as both a RegExp and its source string for parsing
 */
export interface RegexDomain extends Domain<string> {
  type: DomainType.REGEX_DOMAIN;
  pattern: RegExp;
  source: string;
}

/**
 * Alternation domain for values that can match one of several alternatives
 * Stores the domains of each alternative validator
 */
export interface AlternationDomain<T> extends Domain<T> {
  type: DomainType.ALTERNATION_DOMAIN;
  alternatives: Domain<T>[];
}

/**
 * Sequence domain for values that are composed of multiple parts in order
 * Stores the domains of each part validator
 */
export interface SequenceDomain<T> extends Domain<T> {
  type: DomainType.SEQUENCE_DOMAIN;
  parts: Domain<T>[];
}

/**
 * Quantifier domain for repeated values
 * Validates arrays where each element matches the inner domain
 */
export interface QuantifierDomain<T> extends Domain<T[]> {
  type: DomainType.QUANTIFIER_DOMAIN;
  inner: Domain<T>;
  min: number;
  max: number;
}

/**
 * Bytes domain for binary data (Uint8Array)
 * Supports both variable-length (Bytes) and fixed-length (Fixed) binary
 */
export interface BytesDomain extends Domain<Uint8Array> {
  type: DomainType.BYTES_DOMAIN;
  minLength: number;
  maxLength: number;
}

/**
 * BigInt domain for 64-bit integer values (and beyond)
 * Uses JavaScript's BigInt for arbitrary precision integers
 */
export interface BigIntDomain extends Domain<bigint> {
  type: DomainType.BIGINT_DOMAIN;
  min: bigint;
  max: bigint;
}

// Re-export ContiguousType for convenience
export { ContiguousType, ContiguousTypeValue } from './domains/interpolate/ContiguousType';

