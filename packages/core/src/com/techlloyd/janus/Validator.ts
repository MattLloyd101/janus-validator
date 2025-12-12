import { ValidationResult } from './ValidationResult';
import { Domain } from './Domain';
import { Generator } from './Generator';
import { defaultRng } from './RNG';

/**
 * A validator validates values and exposes a domain
 */
export interface Validator<T> {
  /**
   * Validates a value and returns a result
   */
  validate(value: unknown): ValidationResult<T>;

  /**
   * The domain of valid values for this validator
   */
  domain: Domain<T>;
}

/**
 * Base class for validators providing helper methods for creating validation results.
 * 
 * Validators can extend this class to use `this.error()`, `this.success()`, etc.
 * 
 * @example
 * ```typescript
 * class MyValidator extends BaseValidator<number> {
 *   domain = { type: DomainType.CONTIGUOUS_DOMAIN, ... };
 *   
 *   validate(value: unknown): ValidationResult<number> {
 *     if (typeof value !== 'number') {
 *       return this.error('Expected number');
 *     }
 *     return this.success(value);
 *   }
 * }
 * ```
 */
export abstract class BaseValidator<T> implements Validator<T> {
  abstract domain: Domain<T>;
  abstract validate(value: unknown): ValidationResult<T>;

  /**
   * Protected generator instance for creating examples.
   */
  protected generator: Generator;

  /**
   * Creates a new BaseValidator.
   * @param generator Optional generator for creating examples. If not provided,
   *                  a default generator will be created.
   */
  constructor(generator?: Generator) {
    this.generator = generator ?? new Generator(defaultRng);
  }

  /**
   * Format a value for error messages.
   */
  protected formatValue(input: unknown): string {
    if (input === null) return 'null';
    if (input === undefined) return 'undefined';
    if (typeof input === 'number' && Number.isNaN(input)) return 'NaN';
    if (input === Number.POSITIVE_INFINITY) return 'Infinity';
    if (input === Number.NEGATIVE_INFINITY) return '-Infinity';
    if (typeof input === 'string') return `"${input}"`;
    return String(input);
  }

  /**
   * Flatten nested validation results to a single error string.
   */
  private flattenResults(
    results: { [key: string]: ValidationResult<unknown> } | ValidationResult<unknown>[],
    prefix: string = ''
  ): string {
    if (Array.isArray(results)) {
      return results
        .map((r, i) => {
          if (r.valid) return null;
          const path = `${prefix}[${i}]`;
          if (r.results) {
            return this.flattenResults(r.results, path);
          }
          return `${path}: ${r.error}`;
        })
        .filter((s): s is string => s !== null)
        .join('; ');
    }

    return Object.entries(results)
      .map(([key, r]) => {
        if (r.valid) return null;
        const path = prefix ? `${prefix}.${key}` : key;
        if (r.results) {
          return this.flattenResults(r.results, path);
        }
        return `${path}: ${r.error}`;
      })
      .filter((s): s is string => s !== null)
      .join('; ');
  }

  /**
   * Create a validation failure result with an auto-generated example.
   * @internal
   */
  error(message: string): ValidationResult<T> {
    try {
      const example = this.generator.generate(this.domain);
      return { valid: false, error: message, example };
    } catch {
      return { valid: false, error: message };
    }
  }

  /**
   * Create a validation success result.
   * @internal
   */
  success(value: T): ValidationResult<T> {
    return { valid: true, value };
  }

  /**
   * Create a validation failure result for an object with per-field results.
   * Derives example from child results, or generates a complete example if needed.
   * @internal
   */
  objectError(results: { [key: string]: ValidationResult<unknown> }): ValidationResult<T> {
    const errorMsg = this.flattenResults(results);
    
    // Try to derive example from child results
    const example: Record<string, any> = {};
    let hasAllExamples = true;
    
    for (const [key, result] of Object.entries(results)) {
      if (result.valid) {
        example[key] = result.value;
      } else if (result.example !== undefined) {
        example[key] = result.example;
      } else {
        hasAllExamples = false;
      }
    }
    
    if (hasAllExamples && Object.keys(example).length > 0) {
      return { valid: false, error: errorMsg, results, example: example as T };
    }
    
    // Generate a complete example from the validator
    try {
      const generatedExample = this.generator.generate(this.domain);
      return { valid: false, error: errorMsg, results, example: generatedExample };
    } catch {
      return { valid: false, error: errorMsg, results };
    }
  }

  /**
   * Create a validation failure result for an array with per-element results.
   * Derives example from child results, or generates a complete example if needed.
   * @internal
   */
  arrayError(results: ValidationResult<unknown>[]): ValidationResult<T> {
    const errorMsg = this.flattenResults(results);
    
    // Try to derive example from child results
    const example: any[] = [];
    let hasAllExamples = true;
    
    for (const result of results) {
      if (result.valid) {
        example.push(result.value);
      } else if (result.example !== undefined) {
        example.push(result.example);
      } else {
        hasAllExamples = false;
        break;
      }
    }
    
    if (hasAllExamples && example.length === results.length) {
      return { valid: false, error: errorMsg, results, example: example as T };
    }
    
    // Generate a complete example from the validator
    try {
      const generatedExample = this.generator.generate(this.domain);
      return { valid: false, error: errorMsg, results, example: generatedExample };
    } catch {
      return { valid: false, error: errorMsg, results };
    }
  }
}
