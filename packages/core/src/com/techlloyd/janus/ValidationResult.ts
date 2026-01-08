/**
 * Result of a validation check.
 * 
 * A ValidationResult is a discriminated union that represents either:
 * - **Success**: `{ valid: true, value: T }` - validation passed with the validated value
 * - **Failure**: `{ valid: false, error: string, example?: T, results?: ... }` - validation failed
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
 * // Nested struct validation
 * const userValidator = Struct({
 *   name: UnicodeString(1, 100),
 *   age: Integer(0, 150),
 * });
 * 
 * const result = userValidator.validate({ name: "Alice", age: 200 });
 * // {
 * //   valid: false,
 * //   error: "age: Expected value <= 150, got 200",
 * //   results: {
 * //     name: { valid: true, value: "Alice" },
 * //     age: { valid: false, error: "Expected value <= 150, got 200", example: 42 }
 * //   },
 * //   example: { name: "Alice", age: 42 }
 * // }
 * ```
 * 
 * @example
 * ```typescript
 * // Array validation with per-element results
 * const listValidator = Quantifier.oneOrMore(Integer(0, 100));
 * const result = listValidator.validate([50, 150, 25]);
 * // {
 * //   valid: false,
 * //   error: "[1]: Expected value <= 100, got 150",
 * //   results: [
 * //     { valid: true, value: 50 },
 * //     { valid: false, error: "Expected value <= 100, got 150", example: 50 },
 * //     { valid: true, value: 25 }
 * //   ]
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
