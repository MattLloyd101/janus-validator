import { Validator, BaseValidator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { Domain, DomainType } from '../Domain';

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
export interface StructDomain<T = object> extends Domain<T> {
  type: DomainType.STRUCT_DOMAIN;
  schema: { [key: string]: Domain<any> };
  strict: boolean;
}

/**
 * Validator for objects with a specified schema.
 * 
 * Each property in the schema is validated against its corresponding validator.
 * In strict mode, extra properties not in the schema will cause validation to fail.
 * 
 * On failure, returns a recursive ValidationResult with per-field results,
 * showing which fields passed and which failed (with examples at each level).
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
export class StructValidator<S extends StructSchema> extends BaseValidator<InferStructType<S>> {
  public readonly domain: StructDomain<InferStructType<S>>;
  private readonly schemaKeys: string[];

  constructor(
    public readonly schema: S,
    public readonly strict: boolean = false
  ) {
    super();
    this.schemaKeys = Object.keys(schema);
    this.domain = {
      type: DomainType.STRUCT_DOMAIN,
      schema: Object.fromEntries(
        this.schemaKeys.map(key => [key, schema[key].domain])
      ),
      strict,
    };
  }

  validate(input: unknown): ValidationResult<InferStructType<S>> {
    // Check if input is an object
    if (input === null || typeof input !== 'object' || Array.isArray(input)) {
      return this.error(
        `Expected object, got ${input === null ? 'null' : Array.isArray(input) ? 'array' : typeof input}`
      );
    }

    const inputObj = input as Record<string, unknown>;
    const inputKeys = Object.keys(inputObj);
    const results: { [key: string]: ValidationResult<any> } = {};
    const validatedObj: Record<string, any> = {};
    let hasErrors = false;

    // In strict mode, check for extra properties
    if (this.strict) {
      const extraKeys = inputKeys.filter(key => !this.schemaKeys.includes(key));
      for (const key of extraKeys) {
        results[key] = { valid: false, error: 'Unexpected property' };
        hasErrors = true;
      }
    }

    // Validate each property in the schema
    for (const key of this.schemaKeys) {
      if (!(key in inputObj)) {
        // For missing property, validate undefined to get an error with example
        const fieldValidator = this.schema[key];
        results[key] = fieldValidator.validate(undefined);
        if (results[key].valid) {
          // Field accepts undefined
          validatedObj[key] = results[key].value;
        } else {
          // Replace error message with "Missing required property"
          results[key] = { ...results[key], error: 'Missing required property' };
          hasErrors = true;
        }
        continue;
      }

      const fieldValidator = this.schema[key];
      const result = fieldValidator.validate(inputObj[key]);
      results[key] = result;

      if (!result.valid) {
        hasErrors = true;
      } else {
        validatedObj[key] = result.value;
      }
    }

    if (hasErrors) {
      return this.objectError(results);
    }

    // In non-strict mode, preserve extra properties
    if (!this.strict) {
      for (const key of inputKeys) {
        if (!this.schemaKeys.includes(key)) {
          validatedObj[key] = inputObj[key];
        }
      }
    }

    return this.success(validatedObj as InferStructType<S>);
  }
}

/**
 * Creates a validator for objects with a specified schema.
 */
export function Struct<S extends StructSchema>(
  schema: S,
  strict: boolean = false
): StructValidator<S> {
  return new StructValidator(schema, strict);
}
