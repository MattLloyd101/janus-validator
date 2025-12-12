import { Validator, ValidationResult, RNG, Generator } from '../index';

/**
 * Default RNG using Math.random
 */
const defaultRng: RNG = {
  random: () => Math.random(),
};

/**
 * Wraps a validator to include an example of a valid value when validation fails.
 * 
 * This is useful for providing helpful feedback to users by showing them
 * what a valid value would look like.
 * 
 * @param validator The validator to wrap
 * @param rng Optional RNG for generating examples (defaults to Math.random)
 * 
 * @example
 * ```typescript
 * const validator = withExample(Integer(0, 100));
 * 
 * const result = validator.validate('not a number');
 * // result = {
 * //   valid: false,
 * //   error: 'Expected number, got string',
 * //   example: 42  // A valid example
 * // }
 * ```
 */
export function withExample<T>(
  validator: Validator<T>,
  rng: RNG = defaultRng
): Validator<T> {
  const generator = new Generator(rng);

  return {
    validate: (input: unknown): ValidationResult<T> => {
      const result = validator.validate(input);
      
      if (!result.valid) {
        try {
          const example = generator.generate(validator);
          return {
            valid: false,
            error: result.error,
            results: result.results,
            example,
          };
        } catch {
          // If generation fails, return result without example
          return result;
        }
      }
      
      return result;
    },
    domain: validator.domain,
  };
}

/**
 * Creates a validator that always includes examples in error messages.
 * This is a convenience wrapper around withExample.
 * 
 * @param createValidator Function that creates the validator
 * @param rng Optional RNG for generating examples
 */
export function validatorWithExample<T, Args extends any[]>(
  createValidator: (...args: Args) => Validator<T>,
  rng: RNG = defaultRng
): (...args: Args) => Validator<T> {
  return (...args: Args) => withExample(createValidator(...args), rng);
}

