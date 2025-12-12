/**
 * Domain classes for validation and generation.
 *
 * Domains represent the set of valid values for a validator and are used for:
 * - generation (via domain generator strategies)
 * - compatibility reasoning (`encapsulates`)
 */

// Types and utilities
export {
  DomainType,
  RelationResult,
  ok,
  no,
  unknown,
} from './types';

// CharRange utilities (for CharSetDomain and regex character classes)
export {
  CharRange,
  normalizeRanges,
  rangesSize,
  rangesSubset,
  charsToRanges,
  charRange,
} from './CharRange';

// Base class
export { Domain } from './Domain';

// Concrete domain classes
export { FiniteDomain } from './FiniteDomain';
export { StringDomain } from './StringDomain';
export { CharSetDomain } from './CharSetDomain';
export { ContiguousDomain } from './ContiguousDomain';
export { RegexDomain } from './RegexDomain';
export { AlternationDomain } from './AlternationDomain';
export { SequenceDomain } from './SequenceDomain';
export { QuantifierDomain } from './QuantifierDomain';
export { BytesDomain } from './BytesDomain';
export { BigIntDomain } from './BigIntDomain';
export { StructDomain } from './StructDomain';
export { CustomGeneratorDomain } from './CustomGeneratorDomain';

// Re-export ContiguousType for convenience
export { ContiguousType, ContiguousTypeValue } from '../generators/interpolate/ContiguousType';
