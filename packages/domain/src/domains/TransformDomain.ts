import { BaseDomain, Domain } from "../Domain";
import { DomainType } from "../types";

/**
 * Domain that transforms values from an inner domain.
 * 
 * This domain wraps another domain and applies a transformation function
 * to values generated from it. It's used to support `.transform()` operations
 * on validators.
 * 
 * **Generation**: Generates a value from the inner domain, then applies the transform.
 * 
 * **Contains**: Cannot accurately check containment without an inverse transform,
 * so this method returns `true` conservatively to avoid false negatives.
 * For accurate validation, use the validator, not `domain.contains()`.
 * 
 * @typeParam TIn - The input type (from the inner domain)
 * @typeParam TOut - The output type (after transformation)
 * @typeParam D - The inner domain type
 * 
 * @example
 * ```typescript
 * const stringDomain = new StringDomain({ minLength: 1, maxLength: 50 });
 * const upperDomain = new TransformDomain(stringDomain, s => s.toUpperCase());
 * 
 * // Generation: generates "hello" → transforms to "HELLO"
 * generator.generate(upperDomain); // "HELLO"
 * 
 * // Contains: returns true conservatively
 * upperDomain.contains("HELLO"); // true (but doesn't verify it came from transform)
 * ```
 */
export class TransformDomain<TIn, TOut, D extends Domain<TIn> = Domain<TIn>> extends BaseDomain<TOut> {
  readonly kind = DomainType.TRANSFORM;

  constructor(
    /** The inner domain to generate/validate from */
    public readonly inner: D,
    /** The transformation function to apply */
    public readonly transform: (value: TIn) => TOut
  ) {
    super();
  }

  /**
   * Checks if a value belongs to this domain.
   * 
   * **Note**: Cannot accurately check containment without an inverse transform.
   * This method returns `true` conservatively to avoid false negatives.
   * For accurate validation, use the validator's `validate()` method.
   * 
   * @param value - The value to check
   * @returns Always `true` (conservative approximation)
   */
  contains(value: unknown): value is TOut {
    // We cannot invert the transform to check if value came from the inner domain.
    // Return true conservatively to avoid false negatives.
    // Actual validation should use the validator, not domain.contains().
    return true;
  }
}
