/**
 * Domain classes for validation and generation.
 *
 * Domains represent the set of valid values for a validator and are used for:
 * - generation (via domain generator strategies)
 * - compatibility reasoning (`encapsulates`)
 */

// Public types
export { DomainType, RelationResult } from './types';

// Internal utilities - not part of public API but needed by other internal modules
export { ok, no, unknown } from './types';
export { normalizeRanges, rangesSize, rangesSubset } from './CharRange';

// CharRange - public API for creating character sets
export { CharRange, charsToRanges, charRange } from './CharRange';

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

// Internal - generator implementation details
export { ContiguousType, ContiguousTypeValue } from '../generators/interpolate/ContiguousType';
