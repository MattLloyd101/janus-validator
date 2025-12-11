/**
 * @janus-validator/avro
 *
 * Avro schema import/export for Janus Validator
 *
 * This package provides bidirectional conversion between Avro schemas
 * and Janus validators. Since Avro doesn't natively support validation
 * constraints, we use x-janus-* prefixed fields in the schema.
 *
 * @example
 * ```typescript
 * import { avroToValidator, validatorToAvro } from '@janus-validator/avro';
 *
 * // Convert Avro schema to validator
 * const validator = avroToValidator(avroSchema);
 *
 * // Convert validator to Avro schema
 * const schema = validatorToAvro(validator);
 * ```
 */

export { avroToValidator } from './com/techlloyd/janus/AvroToValidator';
export { validatorToAvro } from './com/techlloyd/janus/ValidatorToAvro';
export type { AvroSchema, ExtendedAvroSchema, JanusAvroExtensions } from './com/techlloyd/janus/types';

