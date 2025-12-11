/**
 * Janus-specific extensions for Avro schemas
 * These are prefixed with x-janus- to indicate non-standard fields
 */
export interface JanusAvroExtensions {
  /** Minimum value for numeric types */
  'x-janus-min'?: number;
  /** Maximum value for numeric types */
  'x-janus-max'?: number;
  /** Minimum length for string/bytes types */
  'x-janus-minLength'?: number;
  /** Maximum length for string/bytes types */
  'x-janus-maxLength'?: number;
  /** Regex pattern for string types */
  'x-janus-pattern'?: string;
  /** Array of allowed constant values */
  'x-janus-enum'?: unknown[];
  /** Minimum number of items for array types */
  'x-janus-minItems'?: number;
  /** Maximum number of items for array types */
  'x-janus-maxItems'?: number;
  /** Description of the field */
  'x-janus-description'?: string;
  /** Example values for generation hints */
  'x-janus-examples'?: unknown[];
}

/**
 * Base Avro primitive types
 */
export type AvroPrimitiveType =
  | 'null'
  | 'boolean'
  | 'int'
  | 'long'
  | 'float'
  | 'double'
  | 'bytes'
  | 'string';

/**
 * Avro array type
 */
export interface AvroArrayType {
  type: 'array';
  items: AvroType;
}

/**
 * Avro map type
 */
export interface AvroMapType {
  type: 'map';
  values: AvroType;
}

/**
 * Avro enum type
 */
export interface AvroEnumType {
  type: 'enum';
  name: string;
  symbols: string[];
  namespace?: string;
  doc?: string;
}

/**
 * Avro fixed type
 */
export interface AvroFixedType {
  type: 'fixed';
  name: string;
  size: number;
  namespace?: string;
}

/**
 * Avro record field
 */
export interface AvroField extends JanusAvroExtensions {
  name: string;
  type: AvroType;
  doc?: string;
  default?: unknown;
  order?: 'ascending' | 'descending' | 'ignore';
  aliases?: string[];
}

/**
 * Avro record type
 */
export interface AvroRecordType extends JanusAvroExtensions {
  type: 'record';
  name: string;
  fields: AvroField[];
  namespace?: string;
  doc?: string;
  aliases?: string[];
}

/**
 * Union type (represented as array of types)
 */
export type AvroUnionType = AvroType[];

/**
 * All possible Avro types
 */
export type AvroType =
  | AvroPrimitiveType
  | AvroArrayType
  | AvroMapType
  | AvroEnumType
  | AvroFixedType
  | AvroRecordType
  | AvroUnionType;

/**
 * Extended Avro schema with Janus validation extensions
 */
export type ExtendedAvroSchema = AvroType & JanusAvroExtensions;

/**
 * Top-level Avro schema (typically a record or named type)
 */
export type AvroSchema = AvroRecordType | AvroEnumType | AvroFixedType | AvroArrayType | AvroPrimitiveType;

