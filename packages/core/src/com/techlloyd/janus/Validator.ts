import { ValidationResult } from './ValidationResult';
import { Domain } from './Domain';

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

