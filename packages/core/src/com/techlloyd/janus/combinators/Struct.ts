import { Validator, ValidationResult, Domain, DomainType } from '../index';

/**
 * Schema definition for Struct validator - maps property names to validators
 */
export type StructSchema = {
  [key: string]: Validator<any>;
};

/**
 * Infer the validated type from a StructSchema
 */
export type InferStructType<S extends StructSchema> = {
  [K in keyof S]: S[K] extends Validator<infer T> ? T : never;
};

/**
 * Domain for struct validators
 */
export interface StructDomain extends Domain<object> {
  type: DomainType.STRUCT_DOMAIN;
  schema: { [key: string]: Domain<any> };
  strict: boolean;
}

/**
 * Creates a validator for objects with a specified schema.
 * 
 * Each property in the schema is validated against its corresponding validator.
 * In strict mode, extra properties not in the schema will cause validation to fail.
 * 
 * @param schema Object mapping property names to validators
 * @param strict If true, reject objects with extra properties (default: false)
 * 
 * @example
 * ```typescript
 * const userValidator = Struct({
 *   name: UnicodeString(1, 100),
 *   age: Integer(0, 150),
 *   active: Boolean()
 * });
 * 
 * userValidator.validate({ name: 'Alice', age: 30, active: true });  // valid
 * userValidator.validate({ name: 'Bob', age: 25 });                   // invalid (missing 'active')
 * 
 * // Strict mode
 * const strictUser = Struct({ name: UnicodeString() }, true);
 * strictUser.validate({ name: 'Alice' });              // valid
 * strictUser.validate({ name: 'Alice', extra: 123 }); // invalid (extra property)
 * ```
 */
export function Struct<S extends StructSchema>(
  schema: S,
  strict: boolean = false
): Validator<InferStructType<S>> {
  const schemaKeys = Object.keys(schema);
  
  return {
    validate: (input: unknown): ValidationResult<InferStructType<S>> => {
      // Check if input is an object
      if (input === null || typeof input !== 'object' || Array.isArray(input)) {
        return {
          valid: false,
          error: `Expected object, got ${input === null ? 'null' : Array.isArray(input) ? 'array' : typeof input}`,
        };
      }

      const inputObj = input as Record<string, unknown>;
      const inputKeys = Object.keys(inputObj);

      // In strict mode, check for extra properties
      if (strict) {
        const extraKeys = inputKeys.filter(key => !schemaKeys.includes(key));
        if (extraKeys.length > 0) {
          return {
            valid: false,
            error: `Unexpected properties: ${extraKeys.join(', ')}`,
          };
        }
      }

      // Validate each property in the schema
      const validatedObj: Record<string, any> = {};

      for (const key of schemaKeys) {
        if (!(key in inputObj)) {
          return {
            valid: false,
            error: `Missing required property: ${key}`,
          };
        }

        const validator = schema[key];
        const result = validator.validate(inputObj[key]);

        if (!result.valid) {
          return {
            valid: false,
            error: `Property '${key}': ${result.error}`,
          };
        }

        validatedObj[key] = result.value;
      }

      // In non-strict mode, preserve extra properties
      if (!strict) {
        for (const key of inputKeys) {
          if (!schemaKeys.includes(key)) {
            validatedObj[key] = inputObj[key];
          }
        }
      }

      return { valid: true, value: validatedObj as InferStructType<S> };
    },
    domain: {
      type: DomainType.STRUCT_DOMAIN,
      schema: Object.fromEntries(
        schemaKeys.map(key => [key, schema[key].domain])
      ),
      strict,
    } as StructDomain,
  };
}

