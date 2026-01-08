import { DomainType } from "./types";

/**
 * A Domain represents the set of valid values for a type.
 * 
 * Domains serve multiple purposes:
 * 1. **Type checking**: The `contains` method determines if a value belongs to the domain
 * 2. **Value generation**: Generators use domains to produce valid test data
 * 3. **Set operations**: Domains can be combined using union, intersection, and subtraction
 * 
 * Each domain type has a `kind` discriminator that identifies its concrete type,
 * enabling type-safe pattern matching in generators and other consumers.
 * 
 * @typeParam T - The type of values contained in this domain
 * 
 * @example
 * ```typescript
 * // A domain for positive integers 1-100
 * const domain: Domain<number> = new ContiguousDomain(1, 100, true);
 * 
 * domain.contains(50);  // true
 * domain.contains(0);   // false
 * domain.contains(3.5); // false (not an integer)
 * ```
 * 
 * @example
 * ```typescript
 * // A domain for specific status values
 * const statusDomain: Domain<string> = new FiniteDomain(['active', 'inactive', 'pending']);
 * 
 * statusDomain.contains('active');   // true
 * statusDomain.contains('unknown');  // false
 * ```
 */
export interface Domain<T = unknown> {
  /**
   * Discriminator that identifies the concrete domain type.
   * Used for type-safe pattern matching in generators and set operations.
   */
  readonly kind: DomainType;

  /**
   * Type guard that checks if a value belongs to this domain.
   * 
   * This method serves as both a membership test and a TypeScript type guard,
   * narrowing the type of `value` to `T` when it returns true.
   * 
   * @param value - The value to check for domain membership
   * @returns `true` if the value is a valid member of this domain, `false` otherwise
   * 
   * @example
   * ```typescript
   * const domain: Domain<number> = new ContiguousDomain(0, 100);
   * const value: unknown = getUserInput();
   * 
   * if (domain.contains(value)) {
   *   // TypeScript now knows `value` is a `number`
   *   console.log(value.toFixed(2));
   * }
   * ```
   */
  contains(value: unknown): value is T;
}

/**
 * Abstract base class for implementing domains.
 * 
 * Extend this class when creating custom domain types. Subclasses must implement:
 * - `kind`: A discriminator from `DomainType` for pattern matching
 * - `contains`: A type guard for checking domain membership
 * 
 * @typeParam T - The type of values contained in this domain
 * 
 * @example
 * ```typescript
 * class EvenNumberDomain extends BaseDomain<number> {
 *   readonly kind = DomainType.CONTIGUOUS; // or define a new DomainType
 * 
 *   contains(value: unknown): value is number {
 *     return typeof value === 'number' && Number.isInteger(value) && value % 2 === 0;
 *   }
 * }
 * ```
 */
export abstract class BaseDomain<T> implements Domain<T> {
  abstract readonly kind: DomainType;
  abstract contains(value: unknown): value is T;
}
