/**
 * Utilities for customizing value generation for validators
 */

import { Validator } from '../Validator';
import { Domain, DomainType } from '../Domain';
import { RNG } from '../RNG';

/**
 * Custom domain type that wraps another domain with custom generation logic
 */
export interface CustomGeneratorDomain<T> extends Domain<T> {
  type: DomainType.CUSTOM_GENERATOR_DOMAIN;
  innerDomain: Domain<T>;
  generate: (rng: RNG) => T;
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
export function withGenerator<T>(
  validator: Validator<T>,
  generate: GeneratorFn<T>
): Validator<T> {
  return {
    validate: validator.validate,
    domain: {
      type: DomainType.CUSTOM_GENERATOR_DOMAIN,
      innerDomain: validator.domain,
      generate,
    } as CustomGeneratorDomain<T>,
  };
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
export function fromValues<T>(
  validator: Validator<T>,
  values: T[]
): Validator<T> {
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
export function fromWeightedValues<T>(
  validator: Validator<T>,
  weightedValues: [T, number][]
): Validator<T> {
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
export function cycleValues<T>(
  validator: Validator<T>,
  values: T[]
): Validator<T> {
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
export function combineGenerators<T>(
  validator: Validator<T>,
  generators: GeneratorFn<T>[]
): Validator<T> {
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
export function templateGenerator<T extends string>(
  validator: Validator<T>,
  template: (pick: <V>(values: V[]) => V, rng: RNG) => T
): Validator<T> {
  return withGenerator(validator, (rng) => {
    const pick = <V>(values: V[]): V => {
      const index = Math.floor(rng.random() * values.length);
      return values[index];
    };
    return template(pick, rng);
  });
}

