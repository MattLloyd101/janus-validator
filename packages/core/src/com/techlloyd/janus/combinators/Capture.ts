import { Validator, BaseValidator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { Domain, DomainType } from '../Domain';

/**
 * Context for storing captured values during validation.
 * Shared between Capture and Ref validators.
 */
export class ValidationContext {
  private captures: Map<string, any> = new Map();

  /**
   * Store a captured value
   */
  set<T>(name: string, value: T): void {
    this.captures.set(name, value);
  }

  /**
   * Retrieve a captured value
   */
  get<T>(name: string): T | undefined {
    return this.captures.get(name);
  }

  /**
   * Check if a capture exists
   */
  has(name: string): boolean {
    return this.captures.has(name);
  }

  /**
   * Clear all captures (useful for reusing context)
   */
  clear(): void {
    this.captures.clear();
  }

  /**
   * Get all captured values
   */
  all(): Record<string, any> {
    return Object.fromEntries(this.captures);
  }
}

/**
 * Domain for captured values - wraps the inner validator's domain
 */
export interface CaptureDomain<T> extends Domain<T> {
  type: DomainType.CAPTURE_DOMAIN;
  name: string;
  inner: Domain<T>;
}

/**
 * Domain for reference validators
 */
export interface RefDomain<T> extends Domain<T> {
  type: DomainType.REF_DOMAIN;
  name: string;
}

/**
 * Capture combinator - validates input and stores the result in context.
 * 
 * @example
 * ```typescript
 * const ctx = new ValidationContext();
 * const validator = O({
 *   password: new Capture(ctx, 'pwd', UnicodeString(8, 50)),
 *   confirmPassword: new Ref(ctx, 'pwd')
 * });
 * ```
 */
export class Capture<T> implements Validator<T> {
  public readonly domain: CaptureDomain<T>;

  constructor(
    private readonly context: ValidationContext,
    public readonly name: string,
    public readonly validator: Validator<T>
  ) {
    this.domain = {
      type: DomainType.CAPTURE_DOMAIN,
      name,
      inner: validator.domain,
    };
  }

  validate(input: unknown): ValidationResult<T> {
    const result = this.validator.validate(input);
    
    if (result.valid) {
      // Store the validated value in context
      this.context.set(this.name, result.value);
    }
    
    return result;
  }
}

/**
 * Ref combinator - validates that input equals a previously captured value.
 * 
 * @example
 * ```typescript
 * const ctx = new ValidationContext();
 * const validator = O({
 *   password: new Capture(ctx, 'pwd', UnicodeString(8, 50)),
 *   confirmPassword: new Ref(ctx, 'pwd')
 * });
 * ```
 */
export class Ref<T> extends BaseValidator<T> {
  public readonly domain: RefDomain<T>;

  constructor(
    private readonly context: ValidationContext,
    public readonly name: string,
    private readonly comparator: (a: unknown, b: T) => boolean = (a, b) => a === b
  ) {
    super();
    this.domain = {
      type: DomainType.REF_DOMAIN,
      name,
    };
  }

  validate(input: unknown): ValidationResult<T> {
    if (!this.context.has(this.name)) {
      return this.error(`Reference '${this.name}' has not been captured yet`);
    }

    const captured = this.context.get<T>(this.name)!;
    
    if (this.comparator(input, captured)) {
      return this.success(input as T);
    }

    return this.error(`Value does not match captured '${this.name}'`);
  }
}

/**
 * Result of createCaptureGroup - provides linked capture/ref functions and shared context.
 */
export interface CaptureGroup {
  capture: <T>(name: string, validator: Validator<T>) => Capture<T>;
  ref: <T>(name: string, comparator?: (a: unknown, b: T) => boolean) => Ref<T>;
  context: ValidationContext;
}

/**
 * Creates a capture group with linked capture and ref functions.
 * 
 * This is the recommended way to use Capture/Ref as it ensures
 * they share the same context.
 * 
 * @example
 * ```typescript
 * const { capture, ref, context } = createCaptureGroup();
 * 
 * const validator = O({
 *   password: capture('pwd', UnicodeString(8, 50)),
 *   confirmPassword: ref('pwd')
 * });
 * 
 * validator.validate({ password: 'secret123', confirmPassword: 'secret123' }); // valid
 * validator.validate({ password: 'secret123', confirmPassword: 'different' }); // invalid
 * 
 * // Clear context between validations if reusing
 * context.clear();
 * ```
 */
export function createCaptureGroup(): CaptureGroup {
  const context = new ValidationContext();
  
  return {
    capture: <T>(name: string, validator: Validator<T>) => new Capture(context, name, validator),
    ref: <T>(name: string, comparator?: (a: unknown, b: T) => boolean) => new Ref(context, name, comparator),
    context,
  };
}
