/**
 * Result of a validation check.
 * 
 * A ValidationResult is a discriminated union that represents either:
 * - **Success**: `{ valid: true, value: T }` - validation passed with the validated value
 * - **Failure**: `{ valid: false, error: string, example?: T, ... }` - validation failed
 * 
 * ## Success Results
 * 
 * When validation succeeds, the result contains the validated (and possibly coerced) value:
 * 
 * ```typescript
 * const result = validator.validate(input);
 * if (result.valid) {
 *   // TypeScript knows result.value is type T
 *   processValue(result.value);
 * }
 * ```
 * 
 * ## Failure Results
 * 
 * When validation fails, the result contains:
 * - `error`: A human-readable error message
 * - `path` (optional): Array of keys/indices showing error location
 * - `pathString` (optional): Dot-notation path for display
 * - `code` (optional): Error code for i18n or programmatic handling
 * - `meta` (optional): Additional metadata attached by validators
 * - `example` (optional): An auto-generated valid example to help users understand the expected format
 * - `results` (optional): For composite types, per-field or per-element sub-results
 * 
 * ## Structured Error Handling
 * 
 * For composite validators (Struct, Sequence, Quantifier), the result is recursive -
 * each child element has its own ValidationResult showing whether it passed or failed,
 * with examples available at each level. This enables:
 * - Detailed form validation with per-field errors
 * - Precise error location in nested structures
 * - Graceful degradation with partial valid data
 * 
 * @typeParam T - The type of the validated value
 * 
 * @example
 * ```typescript
 * // Simple validation
 * const ageValidator = Integer(0, 150);
 * const result = ageValidator.validate(200);
 * // { valid: false, error: "Expected value <= 150, got 200", example: 42 }
 * ```
 * 
 * @example
 * ```typescript
 * // Nested struct validation with paths
 * const userValidator = Struct({
 *   name: UnicodeString(1, 100),
 *   age: Integer(0, 150),
 * });
 * 
 * const result = userValidator.validate({ name: "Alice", age: 200 });
 * // {
 * //   valid: false,
 * //   error: "age: Expected value <= 150, got 200",
 * //   path: ['age'],
 * //   pathString: 'age',
 * //   results: {
 * //     name: { valid: true, value: "Alice" },
 * //     age: { valid: false, error: "Expected value <= 150, got 200", path: ['age'], pathString: 'age' }
 * //   },
 * //   example: { name: "Alice", age: 42 }
 * // }
 * ```
 */
export type ValidationResult<T> =
  | { 
      /** Indicates validation succeeded */
      valid: true; 
      /** The validated (and possibly coerced) value */
      value: T;
    }
  | {
      /** Indicates validation failed */
      valid: false;
      /** Human-readable error message describing what went wrong */
      error: string;
      /** 
       * Path to the error location as array of keys/indices.
       * Example: ['user', 'address', 0, 'zip'] for user.address[0].zip
       */
      path?: (string | number)[];
      /**
       * Path as dot-notation string for display.
       * Example: 'user.address[0].zip'
       */
      pathString?: string;
      /**
       * Error code for i18n or programmatic handling.
       * Example: 'INVALID_EMAIL', 'TOO_SHORT', 'REQUIRED'
       */
      code?: string;
      /**
       * Additional metadata attached by validators.
       */
      meta?: Record<string, unknown>;
      /** 
       * Auto-generated valid example that would pass validation.
       * Useful for showing users the expected format.
       */
      example?: T;
      /** 
       * For composite types (Struct, Sequence, Quantifier): per-field or per-element results.
       * - Object with string keys for Struct validators
       * - Array for Sequence and Quantifier validators
       */
      results?: { [key: string]: ValidationResult<unknown> } | ValidationResult<unknown>[];
    };

/**
 * Helper to format a path array as a human-readable string.
 * 
 * @example
 * ```typescript
 * formatPath(['user', 'addresses', 0, 'zip'])
 * // => 'user.addresses[0].zip'
 * ```
 */
export function formatPath(path: (string | number)[]): string {
  if (path.length === 0) return '';
  
  return path
    .map((segment, i) => {
      if (typeof segment === 'number') {
        return `[${segment}]`;
      }
      return i === 0 ? segment : `.${segment}`;
    })
    .join('');
}

/**
 * Helper to prepend a segment to an error path.
 * Used by composite validators to build up full paths.
 * 
 * @example
 * ```typescript
 * const childResult = { valid: false, error: 'Invalid', path: ['name'] };
 * prependPath(childResult, 'user');
 * // => { valid: false, error: 'Invalid', path: ['user', 'name'], pathString: 'user.name' }
 * ```
 */
export function prependPath<T>(
  result: ValidationResult<T>,
  segment: string | number
): ValidationResult<T> {
  if (result.valid) return result;
  
  const newPath = [segment, ...(result.path ?? [])];
  return {
    ...result,
    path: newPath,
    pathString: formatPath(newPath),
  };
}
