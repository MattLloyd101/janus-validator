/**
 * Janus - A combinator library for defining validators
 *
 * This module provides types and classes for building validators that can:
 * - Validate objects and values
 * - Generate values that match validators using random number generators
 * - Compose complex validators from simple ones
 */

// Core types
export { ValidationResult } from "./ValidationResult";
export { RNG } from "./RNG";
export { Validator, BaseValidator } from "./Validator";
export { Generator } from "./Generator";

// Domain types (for advanced use cases like schema introspection)
export {
  Domain,
  DomainType,
  RelationResult,
  // Domain classes
  FiniteDomain,
  StringDomain,
  CharSetDomain,
  ContiguousDomain,
  RegexDomain,
  AlternationDomain,
  SequenceDomain,
  QuantifierDomain,
  StructDomain,
  CustomGeneratorDomain,
  BytesDomain,
  BigIntDomain,
  // CharRange utilities for creating character sets
  CharRange,
  charRange,
  charsToRanges,
  // ContiguousType for creating ContiguousDomains
  ContiguousType,
} from "./Domain";

// Type utilities for inference
export {
  InferValidatorType,
  UnionOfValidators,
  TupleOfValidators,
  ValidatorSchema,
  InferSchemaType,
} from "./Types";
