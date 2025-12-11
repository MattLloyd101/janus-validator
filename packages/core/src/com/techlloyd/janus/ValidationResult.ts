/**
 * Result of a validation check
 * 
 * When validation fails, optionally includes an example of a valid value.
 */
export type ValidationResult<T> =
  | { valid: true; value: T }
  | { valid: false; error: string; example?: T };

