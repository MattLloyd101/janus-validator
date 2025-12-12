/**
 * Result of a validation check.
 * 
 * For composite validators (Struct, Sequence, Quantifier), the result is recursive -
 * each child element has its own ValidationResult showing whether it passed or failed,
 * with examples available at each level.
 * 
 * @example
 * ```typescript
 * // Validating { name: "Alice", age: 200 } against Struct({ name: String, age: Integer(0,150) })
 * // Returns:
 * {
 *   valid: false,
 *   error: "age: Value 200 is greater than maximum 150",
 *   results: {
 *     name: { valid: true, value: "Alice" },
 *     age: { valid: false, error: "Value 200 is greater than maximum 150", example: 42 }
 *   }
 * }
 * ```
 */
export type ValidationResult<T> =
  | { valid: true; value: T }
  | {
      valid: false;
      error: string;
      example?: T;
      /** For composite types: per-field or per-element results */
      results?: { [key: string]: ValidationResult<unknown> } | ValidationResult<unknown>[];
    };
