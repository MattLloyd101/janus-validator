/**
 * Janus - A combinator library for defining validators
 *
 * This module provides types and classes for building validators that can:
 * - Validate objects and values
 * - Generate values that match validators using random number generators
 * - Compose complex validators from simple ones
 */
export { ValidationResult } from "./ValidationResult";
export { RNG } from "./RNG";
export {
  Domain,
  FiniteDomain,
  StringDomain,
  ContiguousDomain,
  RegexDomain,
  AlternationDomain,
  SequenceDomain,
  QuantifierDomain,
  BytesDomain,
  BigIntDomain,
  DomainType,
  ContiguousType,
  ContiguousTypeValue,
} from "./Domain";
export { Validator } from "./Validator";
export { Generator } from "./Generator";

// Type utilities for inference
export {
  InferValidatorType,
  UnionOfValidators,
  TupleOfValidators,
  ValidatorSchema,
  InferSchemaType,
} from "./Types";
