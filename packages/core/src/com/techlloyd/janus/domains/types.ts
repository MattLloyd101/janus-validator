/**
 * Shared types and utilities for domain definitions.
 */

/**
 * Domain type enum - identifies the kind of domain
 */
export enum DomainType {
  FINITE_DOMAIN = 'FINITE_DOMAIN',
  STRING_DOMAIN = 'STRING_DOMAIN',
  CHARSET_DOMAIN = 'CHARSET_DOMAIN',
  CONTIGUOUS_DOMAIN = 'CONTIGUOUS_DOMAIN',
  REGEX_DOMAIN = 'REGEX_DOMAIN',
  ALTERNATION_DOMAIN = 'ALTERNATION_DOMAIN',
  SEQUENCE_DOMAIN = 'SEQUENCE_DOMAIN',
  QUANTIFIER_DOMAIN = 'QUANTIFIER_DOMAIN',
  STRUCT_DOMAIN = 'STRUCT_DOMAIN',
  CUSTOM_GENERATOR_DOMAIN = 'CUSTOM_GENERATOR_DOMAIN',
  BYTES_DOMAIN = 'BYTES_DOMAIN',
  BIGINT_DOMAIN = 'BIGINT_DOMAIN',
}

/**
 * Result of a domain encapsulation check.
 * - `true`: The domain definitely encapsulates the other
 * - `false`: The domain definitely does not encapsulate the other
 * - `unknown`: Cannot determine (e.g., complex regex comparison)
 */
export type RelationResult =
  | { result: 'true' }
  | { result: 'false'; reason: string }
  | { result: 'unknown'; reason: string };

/** Creates a successful relation result */
export function ok(): RelationResult {
  return { result: 'true' };
}

/** Creates a failed relation result with reason */
export function no(reason: string): RelationResult {
  return { result: 'false', reason };
}

/** Creates an unknown relation result with reason */
export function unknown(reason: string): RelationResult {
  return { result: 'unknown', reason };
}


