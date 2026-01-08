/**
 * Converts Avro schemas to Janus validators
 */

import {
  Validator,
  Domain,
  Null,
  Boolean,
  Integer,
  Long,
  Float,
  UnicodeString,
  Bytes,
  Regex,
  Struct,
  Alternation,
  Quantifier,
  Constant,
} from '@janus-validator/core';
import type {
  AvroSchema,
  AvroType,
  AvroField,
  AvroRecordType,
  AvroArrayType,
  AvroMapType,
  AvroEnumType,
  AvroFixedType,
  JanusAvroExtensions,
} from './types';

/**
 * Options for Avro to Validator conversion
 */
export interface AvroToValidatorOptions {
  /** Whether to use strict mode for record validation (no extra fields). Default: false */
  strict?: boolean;
}

/**
 * Converts an Avro schema to a Janus validator
 *
 * @param schema - The Avro schema to convert
 * @param options - Conversion options
 * @returns A validator that matches the schema
 *
 * @example
 * ```typescript
 * const schema = {
 *   type: 'record',
 *   name: 'User',
 *   fields: [
 *     { name: 'name', type: 'string', 'x-janus-minLength': 1 },
 *     { name: 'age', type: 'int', 'x-janus-min': 0, 'x-janus-max': 150 }
 *   ]
 * };
 *
 * const validator = avroToValidator(schema);
 * validator.validate({ name: 'Alice', age: 30 }); // { valid: true }
 * ```
 */
export function avroToValidator(
  schema: AvroSchema,
  options: AvroToValidatorOptions = {}
): Validator<unknown, Domain<unknown>> {
  return typeToValidator(schema, extractExtensions(schema), options);
}

/**
 * Extracts x-janus-* extensions from an object
 */
function extractExtensions(obj: unknown): JanusAvroExtensions {
  if (typeof obj !== 'object' || obj === null) {
    return {};
  }

  const extensions: JanusAvroExtensions = {};
  const record = obj as Record<string, unknown>;

  if (typeof record['x-janus-min'] === 'number') {
    extensions['x-janus-min'] = record['x-janus-min'];
  }
  if (typeof record['x-janus-max'] === 'number') {
    extensions['x-janus-max'] = record['x-janus-max'];
  }
  if (typeof record['x-janus-minLength'] === 'number') {
    extensions['x-janus-minLength'] = record['x-janus-minLength'];
  }
  if (typeof record['x-janus-maxLength'] === 'number') {
    extensions['x-janus-maxLength'] = record['x-janus-maxLength'];
  }
  if (typeof record['x-janus-pattern'] === 'string') {
    extensions['x-janus-pattern'] = record['x-janus-pattern'];
  }
  if (Array.isArray(record['x-janus-enum'])) {
    extensions['x-janus-enum'] = record['x-janus-enum'];
  }
  if (typeof record['x-janus-minItems'] === 'number') {
    extensions['x-janus-minItems'] = record['x-janus-minItems'];
  }
  if (typeof record['x-janus-maxItems'] === 'number') {
    extensions['x-janus-maxItems'] = record['x-janus-maxItems'];
  }

  return extensions;
}

/**
 * Converts an Avro type to a Janus validator
 */
function typeToValidator(
  type: AvroType,
  extensions: JanusAvroExtensions,
  options: AvroToValidatorOptions
): Validator<unknown, Domain<unknown>> {
  // Handle union types (arrays of types)
  if (Array.isArray(type)) {
    return unionToValidator(type, options);
  }

  // Handle primitive types (strings)
  if (typeof type === 'string') {
    return primitiveToValidator(type, extensions);
  }

  // Handle complex types (objects with 'type' property)
  if (typeof type === 'object' && type !== null) {
    const complexType = type as { type: string };

    switch (complexType.type) {
      case 'record':
        return recordToValidator(type as AvroRecordType, options);
      case 'array':
        return arrayToValidator(type as AvroArrayType, extensions, options);
      case 'map':
        return mapToValidator(type as AvroMapType, options);
      case 'enum':
        return enumToValidator(type as AvroEnumType);
      case 'fixed':
        return fixedToValidator(type as AvroFixedType);
      default:
        throw new Error(`Unknown Avro type: ${complexType.type}`);
    }
  }

  throw new Error(`Invalid Avro type: ${JSON.stringify(type)}`);
}

/**
 * Converts an Avro primitive type to a Janus validator
 */
function primitiveToValidator(
  type: string,
  extensions: JanusAvroExtensions
): Validator<unknown, Domain<unknown>> {
  // If x-janus-enum is present, use Constant/Alternation for finite values
  if (extensions['x-janus-enum'] && extensions['x-janus-enum'].length > 0) {
    const values = extensions['x-janus-enum'];
    if (values.length === 1) {
      return Constant(values[0]);
    }
    return Alternation.of(...values.map((v) => Constant(v)));
  }

  switch (type) {
    case 'null':
      return Null();

    case 'boolean':
      return Boolean();

    case 'int':
      return Integer(
        extensions['x-janus-min'] ?? undefined,
        extensions['x-janus-max'] ?? undefined
      );

    case 'long':
      return Long(
        extensions['x-janus-min'] !== undefined
          ? BigInt(extensions['x-janus-min'])
          : undefined,
        extensions['x-janus-max'] !== undefined
          ? BigInt(extensions['x-janus-max'])
          : undefined
      );

    case 'float':
    case 'double':
      return Float(
        extensions['x-janus-min'] ?? undefined,
        extensions['x-janus-max'] ?? undefined
      );

    case 'string':
      // If pattern is specified, use Regex validator
      if (extensions['x-janus-pattern']) {
        return Regex(new RegExp(extensions['x-janus-pattern']));
      }
      // Otherwise use UnicodeString with length constraints
      return UnicodeString(
        extensions['x-janus-minLength'] ?? undefined,
        extensions['x-janus-maxLength'] ?? undefined
      );

    case 'bytes':
      return Bytes(
        extensions['x-janus-minLength'] ?? undefined,
        extensions['x-janus-maxLength'] ?? undefined
      );

    default:
      throw new Error(`Unknown Avro primitive type: ${type}`);
  }
}

/**
 * Converts an Avro record to a Janus Struct validator
 */
function recordToValidator(
  record: AvroRecordType,
  options: AvroToValidatorOptions
): Validator<unknown, Domain<unknown>> {
  const schema: Record<string, Validator<unknown, Domain<unknown>>> = {};

  for (const field of record.fields) {
    schema[field.name] = fieldToValidator(field, options);
  }

  return Struct(schema, options.strict ?? false);
}

/**
 * Converts an Avro field to a validator
 */
function fieldToValidator(
  field: AvroField,
  options: AvroToValidatorOptions
): Validator<unknown, Domain<unknown>> {
  const extensions = extractExtensions(field);

  // Handle optional fields (union with null)
  if (Array.isArray(field.type)) {
    const types = field.type;
    const hasNull = types.includes('null');
    const nonNullTypes = types.filter((t) => t !== 'null');

    if (hasNull && nonNullTypes.length === 1) {
      // Optional field: T | null
      const innerValidator = typeToValidator(nonNullTypes[0], extensions, options);
      return Alternation.of(innerValidator, Null());
    }
  }

  return typeToValidator(field.type, extensions, options);
}

/**
 * Converts an Avro union to an Alternation validator
 */
function unionToValidator(
  types: AvroType[],
  options: AvroToValidatorOptions
): Validator<unknown, Domain<unknown>> {
  if (types.length === 0) {
    throw new Error('Empty union type is not allowed');
  }

  if (types.length === 1) {
    return typeToValidator(types[0], {}, options);
  }

  const validators = types.map((t) => typeToValidator(t, extractExtensions(t), options));
  return Alternation.of(...validators);
}

/**
 * Converts an Avro array to a Quantifier validator
 */
function arrayToValidator(
  arrayType: AvroArrayType,
  extensions: JanusAvroExtensions,
  options: AvroToValidatorOptions
): Validator<unknown, Domain<unknown>> {
  const itemValidator = typeToValidator(arrayType.items, {}, options);

  const minItems = extensions['x-janus-minItems'] ?? 0;
  const maxItems = extensions['x-janus-maxItems'] ?? Infinity;

  return new Quantifier(itemValidator, minItems, maxItems);
}

/**
 * Converts an Avro map to a Struct validator (non-strict, per ADR-001)
 *
 * Note: Avro maps are converted to non-strict empty structs because:
 * 1. We don't have a dedicated Map combinator
 * 2. This allows any object shape but doesn't validate values
 * See ADR-001 for design rationale.
 */
function mapToValidator(
  _mapType: AvroMapType,
  _options: AvroToValidatorOptions
): Validator<unknown, Domain<unknown>> {
  // Per ADR-001: Map types become empty non-strict structs
  // This accepts any object but doesn't validate values
  return Struct({}, false);
}

/**
 * Converts an Avro enum to an Alternation of Constants
 */
function enumToValidator(enumType: AvroEnumType): Validator<unknown, Domain<unknown>> {
  if (enumType.symbols.length === 0) {
    throw new Error('Enum must have at least one symbol');
  }

  if (enumType.symbols.length === 1) {
    return Constant(enumType.symbols[0]);
  }

  return Alternation.of(...enumType.symbols.map((s) => Constant(s)));
}

/**
 * Converts an Avro fixed type to a Bytes validator with exact length
 */
function fixedToValidator(fixedType: AvroFixedType): Validator<unknown, Domain<unknown>> {
  // Fixed is bytes with exact length
  return Bytes(fixedType.size, fixedType.size);
}
