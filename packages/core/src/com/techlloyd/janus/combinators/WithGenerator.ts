/**
 * Utilities for customizing value generation for validators
 */

import { BaseValidator, Validator } from '../Validator';
import { RNG } from '../RNG';
import { ValidationResult } from '../ValidationResult';
import { CustomGeneratorDomain, Domain } from '../Domain';

class WithGeneratorValidator<T, D extends Domain<T>, V extends Validator<T, D>> extends BaseValidator<T, CustomGeneratorDomain<T, D>> {
  public readonly domain: CustomGeneratorDomain<T, D>;

  constructor(
    private readonly inner: V,
    generate: GeneratorFn<T>
  ) {
    super();
    this.domain = new CustomGeneratorDomain<T, D>(inner.domain, generate);
  }

  validate(value: unknown): ValidationResult<T> {
    const result = this.inner.validate(value);
    if (result.valid) {
      return this.success(result.value);
    }

    // Preserve the underlying error/results, but generate the example from THIS validator
    // so CUSTOM_GENERATOR_DOMAIN is respected.
    try {
      const example = this._example();
      return { valid: false, error: result.error, results: result.results, example };
    } catch {
      return { valid: false, error: result.error, results: result.results };
    }
  }

  /**
   * Generate an example for this validator using the shared Generator in BaseValidator.
   * Kept as a tiny helper to keep validate() readable.
   */
  private _example(): T {
    // BaseValidator.error() already handles try/catch; we need the raw example value here.
    // We intentionally call the generator indirectly by triggering error() then reading example.
    const res = this.error('__example__');
    if (res.valid) {
      throw new Error('Unexpected valid result');
    }
    if (res.example === undefined) {
      throw new Error('Example generation failed');
    }
    return res.example;
  }
}

/**
 * A function that generates values of type T
 */
export type GeneratorFn<T> = (rng: RNG) => T;

/**
 * A function that selects from a list of values
 */
export type SelectorFn<T> = (values: T[], rng: RNG) => T;

/**
 * Wraps a validator with custom generation logic.
 * The validation behavior remains unchanged, only the generation is customized.
 *
 * @param validator The original validator
 * @param generate A function that generates values using an RNG
 * @returns A new validator with custom generation
 *
 * @example
 * ```typescript
 * // Create a name validator with realistic names
 * const nameValidator = withGenerator(
 *   UnicodeString(1, 50),
 *   (rng) => {
 *     const names = ['Alice', 'Bob', 'Charlie', 'Diana', 'Eve'];
 *     return names[Math.floor(rng.random() * names.length)];
 *   }
 * );
 * ```
 */
export function withGenerator<T, D extends Domain<T>>(
  validator: Validator<T, D>,
  generate: GeneratorFn<T>
): Validator<T, CustomGeneratorDomain<T, D>> {
  return new WithGeneratorValidator(validator, generate);
}

/**
 * Creates a validator that generates from a fixed set of values.
 * Validation still uses the original validator's rules.
 *
 * @param validator The original validator
 * @param values Array of values to randomly select from when generating
 * @returns A new validator that generates from the provided values
 *
 * @example
 * ```typescript
 * const firstNameValidator = fromValues(UnicodeString(1, 50), [
 *   'Alice', 'Bob', 'Charlie', 'Diana', 'Eve', 'Frank'
 * ]);
 * ```
 */
export function fromValues<T, D extends Domain<T>>(
  validator: Validator<T, D>,
  values: T[]
): Validator<T, CustomGeneratorDomain<T, D>> {
  if (values.length === 0) {
    throw new Error('fromValues requires at least one value');
  }

  return withGenerator(validator, (rng) => {
    const index = Math.floor(rng.random() * values.length);
    return values[index];
  });
}

/**
 * Creates a validator that generates using weighted random selection.
 *
 * @param validator The original validator
 * @param weightedValues Array of [value, weight] tuples
 * @returns A new validator that generates using weighted selection
 *
 * @example
 * ```typescript
 * const statusValidator = fromWeightedValues(UnicodeString(), [
 *   ['active', 0.7],    // 70% chance
 *   ['pending', 0.2],   // 20% chance
 *   ['inactive', 0.1],  // 10% chance
 * ]);
 * ```
 */
export function fromWeightedValues<T, D extends Domain<T>>(
  validator: Validator<T, D>,
  weightedValues: [T, number][]
): Validator<T, CustomGeneratorDomain<T, D>> {
  if (weightedValues.length === 0) {
    throw new Error('fromWeightedValues requires at least one value');
  }

  const totalWeight = weightedValues.reduce((sum, [, weight]) => sum + weight, 0);

  return withGenerator(validator, (rng) => {
    let random = rng.random() * totalWeight;
    for (const [value, weight] of weightedValues) {
      random -= weight;
      if (random <= 0) {
        return value;
      }
    }
    // Fallback to last value (shouldn't happen with proper weights)
    return weightedValues[weightedValues.length - 1][0];
  });
}

/**
 * Creates a validator that cycles through values in order.
 * Useful for deterministic test data generation.
 *
 * @param validator The original validator
 * @param values Array of values to cycle through
 * @returns A new validator that generates values in sequence
 *
 * @example
 * ```typescript
 * const dayValidator = cycleValues(UnicodeString(), ['Mon', 'Tue', 'Wed', 'Thu', 'Fri']);
 * // Generates: Mon, Tue, Wed, Thu, Fri, Mon, Tue, ...
 * ```
 */
export function cycleValues<T, D extends Domain<T>>(
  validator: Validator<T, D>,
  values: T[]
): Validator<T, CustomGeneratorDomain<T, D>> {
  if (values.length === 0) {
    throw new Error('cycleValues requires at least one value');
  }

  let index = 0;

  return withGenerator(validator, () => {
    const value = values[index];
    index = (index + 1) % values.length;
    return value;
  });
}

/**
 * Combines multiple generators with equal probability.
 *
 * @param validator The original validator
 * @param generators Array of generator functions
 * @returns A new validator that randomly selects a generator
 *
 * @example
 * ```typescript
 * const emailValidator = combineGenerators(Email(), [
 *   (rng) => `user${Math.floor(rng.random() * 1000)}@gmail.com`,
 *   (rng) => `test${Math.floor(rng.random() * 1000)}@company.com`,
 *   (rng) => `dev${Math.floor(rng.random() * 1000)}@localhost.test`,
 * ]);
 * ```
 */
export function combineGenerators<T, D extends Domain<T>>(
  validator: Validator<T, D>,
  generators: GeneratorFn<T>[]
): Validator<T, CustomGeneratorDomain<T, D>> {
  if (generators.length === 0) {
    throw new Error('combineGenerators requires at least one generator');
  }

  return withGenerator(validator, (rng) => {
    const index = Math.floor(rng.random() * generators.length);
    return generators[index](rng);
  });
}

/**
 * Creates a template-based string generator.
 * Useful for generating structured strings like usernames, emails, etc.
 *
 * @param validator The original validator
 * @param template A function that builds the string using helper generators
 * @returns A new validator with template-based generation
 *
 * @example
 * ```typescript
 * const usernameValidator = templateGenerator(Username(), (pick, rng) => {
 *   const adjectives = ['happy', 'quick', 'clever', 'brave'];
 *   const nouns = ['tiger', 'eagle', 'wolf', 'bear'];
 *   return `${pick(adjectives)}_${pick(nouns)}${Math.floor(rng.random() * 100)}`;
 * });
 * // Generates: happy_tiger42, clever_wolf87, etc.
 * ```
 */
export function templateGenerator<T extends string, D extends Domain<T>>(
  validator: Validator<T, D>,
  template: (pick: <V>(values: V[]) => V, rng: RNG) => T
): Validator<T, CustomGeneratorDomain<T, D>> {
  return withGenerator(validator, (rng) => {
    const pick = <V>(values: V[]): V => {
      const index = Math.floor(rng.random() * values.length);
      return values[index];
    };
    return template(pick, rng);
  });
}

