import { Validator, BaseValidator } from '../../Validator';
import { ValidationResult } from '../../ValidationResult';
import { Domain, TransformDomain } from '../../Domain';

/**
 * Wrapper validator that transforms the validated value.
 * 
 * This validator composes with any existing validator. After the inner validator
 * successfully validates the input, the transform function is applied to produce
 * the output value.
 * 
 * @typeParam TIn - Input type (what the inner validator produces)
 * @typeParam TOut - Output type (what the transform produces)
 * @typeParam D - The inner domain type
 * 
 * @example
 * ```typescript
 * // String trimming
 * const trimmed = new TransformValidator(UnicodeString(1, 100), s => s.trim());
 * trimmed.validate("  hello  "); // { valid: true, value: "hello" }
 * 
 * // Type transformation
 * const toNumber = new TransformValidator(UnicodeString(), s => parseInt(s, 10));
 * toNumber.validate("42"); // { valid: true, value: 42 }
 * 
 * // Transform error handling
 * const risky = new TransformValidator(UnicodeString(), s => JSON.parse(s));
 * risky.validate("not json"); // { valid: false, error: "Transform failed: ..." }
 * ```
 */
export class TransformValidator<TIn, TOut, D extends Domain<TIn>> 
  extends BaseValidator<TOut, TransformDomain<TIn, TOut, D>> {
  
  public readonly domain: TransformDomain<TIn, TOut, D>;

  constructor(
    private readonly inner: Validator<TIn, D>,
    private readonly transformFn: (value: TIn) => TOut,
    private readonly errorMessage?: string
  ) {
    super();
    this.domain = new TransformDomain(inner.domain, transformFn);
  }

  validate(value: unknown): ValidationResult<TOut> {
    // First validate with inner validator
    const innerResult = this.inner.validate(value);
    
    if (!innerResult.valid) {
      // Pass through inner error, but with transformed example if possible
      if (innerResult.example !== undefined) {
        try {
          const example = this.transformFn(innerResult.example as TIn);
          return { ...innerResult, example } as ValidationResult<TOut>;
        } catch {
          // If transform fails on example, just return without example
          return innerResult as unknown as ValidationResult<TOut>;
        }
      }
      return innerResult as unknown as ValidationResult<TOut>;
    }

    // Apply transformation
    try {
      const transformed = this.transformFn(innerResult.value);
      return { valid: true, value: transformed };
    } catch (e) {
      const msg = this.errorMessage ?? 
        `Transform failed: ${e instanceof Error ? e.message : String(e)}`;
      return this.error(msg);
    }
  }
}

/**
 * Creates a validator that transforms the validated value.
 * 
 * @param validator The inner validator
 * @param transformFn The transformation function
 * @param errorMessage Optional custom error message for transform failures
 * @returns A new validator that applies the transform after validation
 * 
 * @example
 * ```typescript
 * // Basic transform
 * const trimmed = transform(U(1, 100), s => s.trim());
 * 
 * // Type-changing transform
 * const toInt = transform(U(), s => parseInt(s, 10));
 * 
 * // With custom error message
 * const parseDate = transform(
 *   U(),
 *   s => new Date(s),
 *   'Please provide a valid date string'
 * );
 * ```
 */
export function transform<TIn, TOut, D extends Domain<TIn>>(
  validator: Validator<TIn, D>,
  transformFn: (value: TIn) => TOut,
  errorMessage?: string
): Validator<TOut, TransformDomain<TIn, TOut, D>> {
  return new TransformValidator(validator, transformFn, errorMessage);
}
