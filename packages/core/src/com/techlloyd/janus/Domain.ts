/**
 * Domain types and classes for validation and generation.
 *
 * This module re-exports all domain definitions from the `domains` package.
 * For new code, prefer importing directly from `./domains`.
 */

export {
  // Types and utilities
  DomainType,
  RelationResult,
  ok,
  no,
  unknown,
  CharRange,
  normalizeRanges,
  rangesSize,
  rangesSubset,
  charsToRanges,
  charRange,
  // Base class
  Domain,
  // Concrete domain classes
  FiniteDomain,
  StringDomain,
  CharSetDomain,
  ContiguousDomain,
  RegexDomain,
  AlternationDomain,
  SequenceDomain,
  QuantifierDomain,
  BytesDomain,
  BigIntDomain,
  StructDomain,
  CustomGeneratorDomain,
  // ContiguousType
  ContiguousType,
  ContiguousTypeValue,
} from './domains';
