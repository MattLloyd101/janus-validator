/**
 * Janus - A combinator library for defining validators
 *
 * This module provides types and classes for building validators that can:
 * - Validate objects and values
 * - Generate values that match validators using random number generators
 * - Compose complex validators from simple ones
 */

// Core types
export { ValidationResult, formatPath, prependPath } from "./ValidationResult";
export { RNG } from "./RNG";
export { Validator, BaseValidator } from "./Validator";
export { Generator } from "./Generator";

// Error formatting utilities
export {
  flattenErrors,
  formatErrors,
  errorsToJson,
  getFirstError,
  getErrorAtPath,
  getErrorsByPath,
  type FormattedError,
} from "./errors";

// Domain types (for advanced use cases like schema introspection)
export {
  Domain,
  DomainType,
  // Domain classes
  FiniteDomain,
  StringDomain,
  ContiguousDomain,
  RegexDomain,
  AlternationDomain,
  SequenceDomain,
  QuantifierDomain,
  StructDomain,
  CustomGeneratorDomain,
  BytesDomain,
  BigIntDomain,
} from "./Domain";

// Type utilities for inference
export {
  InferValidatorType,
  UnionOfValidators,
  TupleOfValidators,
  ValidatorSchema,
  InferSchemaType,
} from "./Types";
