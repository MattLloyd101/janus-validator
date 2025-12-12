/**
 * Domain types and classes for validation and generation.
 *
 * This module re-exports public domain definitions from the `domains` package.
 * For internal code, import directly from `./domains`.
 */

export {
  // Public types
  DomainType,
  RelationResult,
  CharRange,
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
  // ContiguousType needed to create ContiguousDomains
  ContiguousType,
} from './domains';
