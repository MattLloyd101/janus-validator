import { ValidationResult } from '../ValidationResult';

/**
 * A flattened error with path, message, and optional code.
 */
export interface FormattedError {
  /** Path to the error location (e.g., 'user.address.zip') */
  path: string;
  /** Human-readable error message */
  message: string;
  /** Error code for i18n or programmatic handling */
  code?: string;
}

/**
 * Flatten a validation result into a list of leaf errors.
 * 
 * For composite validators (Struct, Sequence, Quantifier), this recursively
 * extracts all leaf errors with their full paths.
 * 
 * @example
 * ```typescript
 * const result = User.validate({ profile: { name: '', email: 'bad' } });
 * const errors = flattenErrors(result);
 * // [
 * //   { path: 'profile.name', message: 'Name is required' },
 * //   { path: 'profile.email', message: 'Invalid email', code: 'INVALID_EMAIL' }
 * // ]
 * ```
 */
export function flattenErrors<T>(result: ValidationResult<T>): FormattedError[] {
  if (result.valid) return [];

  return flattenErrorsRecursive(result, []);
}

/**
 * Internal recursive helper that accumulates path segments.
 */
function flattenErrorsRecursive(
  result: ValidationResult<unknown>,
  pathPrefix: (string | number)[]
): FormattedError[] {
  if (result.valid) return [];

  const errors: FormattedError[] = [];

  // If this result has nested results, recurse into them
  if (result.results) {
    if (Array.isArray(result.results)) {
      for (let i = 0; i < result.results.length; i++) {
        const childResult = result.results[i];
        if (!childResult.valid) {
          errors.push(...flattenErrorsRecursive(childResult, [...pathPrefix, i]));
        }
      }
    } else {
      for (const [key, childResult] of Object.entries(result.results)) {
        if (!childResult.valid) {
          errors.push(...flattenErrorsRecursive(childResult, [...pathPrefix, key]));
        }
      }
    }
  }

  // If we found nested errors, return those; otherwise this is a leaf error
  if (errors.length > 0) {
    return errors;
  }

  // Leaf error - use the accumulated path prefix or the result's own path
  const fullPath = pathPrefix.length > 0 ? pathPrefix : (result.path ?? []);
  return [{
    path: formatPathArray(fullPath),
    message: result.error,
    code: result.code,
  }];
}

/**
 * Format a path array as a string.
 */
function formatPathArray(path: (string | number)[]): string {
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
 * Format validation errors as a human-readable string.
 * 
 * Each error is on its own line, prefixed with its path if available.
 * 
 * @example
 * ```typescript
 * const result = User.validate(invalidData);
 * console.log(formatErrors(result));
 * // profile.name: Name is required
 * // profile.email: Invalid email format
 * ```
 */
export function formatErrors<T>(result: ValidationResult<T>): string {
  if (result.valid) return '';
  
  const errors = flattenErrors(result);
  return errors
    .map(e => e.path ? `${e.path}: ${e.message}` : e.message)
    .join('\n');
}

/**
 * Format validation errors as a JSON object for API responses.
 * 
 * @example
 * ```typescript
 * const result = User.validate(invalidData);
 * res.status(400).json(errorsToJson(result));
 * // {
 * //   valid: false,
 * //   errors: [
 * //     { path: 'profile.name', message: 'Name is required', code: null },
 * //     { path: 'profile.email', message: 'Invalid email', code: 'INVALID_EMAIL' }
 * //   ]
 * // }
 * ```
 */
export function errorsToJson<T>(result: ValidationResult<T>): {
  valid: boolean;
  errors: { path: string | null; message: string; code: string | null }[];
} {
  if (result.valid) {
    return { valid: true, errors: [] };
  }

  const errors = flattenErrors(result);
  return {
    valid: false,
    errors: errors.map(e => ({
      path: e.path || null,
      message: e.message,
      code: e.code ?? null,
    })),
  };
}

/**
 * Get the first error from a validation result.
 * Useful when you only want to show one error at a time.
 * 
 * @example
 * ```typescript
 * const result = User.validate(invalidData);
 * const firstError = getFirstError(result);
 * if (firstError) {
 *   showToast(firstError.message);
 * }
 * ```
 */
export function getFirstError<T>(result: ValidationResult<T>): FormattedError | null {
  if (result.valid) return null;
  
  const errors = flattenErrors(result);
  return errors[0] ?? null;
}

/**
 * Check if a specific path has an error.
 * Useful for form field validation display.
 * 
 * @example
 * ```typescript
 * const result = User.validate(formData);
 * const emailError = getErrorAtPath(result, 'profile.email');
 * if (emailError) {
 *   setFieldError('email', emailError.message);
 * }
 * ```
 */
export function getErrorAtPath<T>(
  result: ValidationResult<T>,
  path: string
): FormattedError | null {
  if (result.valid) return null;
  
  const errors = flattenErrors(result);
  return errors.find(e => e.path === path) ?? null;
}

/**
 * Get all error messages grouped by path.
 * Useful for form validation where a field might have multiple errors.
 * 
 * @example
 * ```typescript
 * const result = User.validate(formData);
 * const errorsByPath = getErrorsByPath(result);
 * // { 'profile.email': ['Invalid email', 'Email is required'] }
 * ```
 */
export function getErrorsByPath<T>(
  result: ValidationResult<T>
): Record<string, string[]> {
  if (result.valid) return {};
  
  const errors = flattenErrors(result);
  const byPath: Record<string, string[]> = {};
  
  for (const error of errors) {
    const key = error.path || '';
    if (!byPath[key]) {
      byPath[key] = [];
    }
    byPath[key].push(error.message);
  }
  
  return byPath;
}
