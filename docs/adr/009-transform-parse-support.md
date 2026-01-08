# ADR-009: Transform and Parse Support via Composition

## Status
Accepted & Implemented

## Date
2026-01-08

## Context

Gap analysis against Zod revealed that janus-validator only validates values—it cannot transform them. This is a significant limitation for real-world use cases:

```typescript
// Zod can parse and transform
const schema = z.string()
  .transform(s => s.trim())
  .transform(s => s.toLowerCase());

schema.parse("  HELLO  "); // → "hello"

// Janus-validator cannot
const validator = U();
validator.validate("  HELLO  "); // → { valid: true, value: "  HELLO  " }
// No way to trim or lowercase
```

Common transformation needs:
- **String normalization**: trim, lowercase, uppercase
- **Type coercion**: string → number, string → Date
- **Parsing**: JSON string → object
- **Sanitization**: remove dangerous characters

### Requirements

1. **`.transform(fn)`** - Transform validated value
2. **`.pipe(validator)`** - Chain validators with type transformation
3. Support chaining multiple transforms
4. Maintain type inference through transforms
5. Handle transform errors gracefully
6. Preserve domain-based generation where possible

## Decision

Implement a **TransformValidator** wrapper that applies a transformation function after successful validation, along with a supporting **TransformDomain** for generation.

### 1. TransformValidator<TIn, TOut>

```typescript
import { Validator, BaseValidator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { Domain } from '../Domain';
import { TransformDomain } from './TransformDomain';

/**
 * Wrapper validator that transforms the validated value.
 * 
 * @typeParam TIn - Input type (what the inner validator produces)
 * @typeParam TOut - Output type (what the transform produces)
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
      try {
        const example = this.transformFn(innerResult.example as TIn);
        return { ...innerResult, example } as ValidationResult<TOut>;
      } catch {
        return innerResult as unknown as ValidationResult<TOut>;
      }
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
 * @param validator The inner validator
 * @param transform The transformation function
 * @param errorMessage Optional custom error message for transform failures
 */
export function transform<TIn, TOut, D extends Domain<TIn>>(
  validator: Validator<TIn, D>,
  transformFn: (value: TIn) => TOut,
  errorMessage?: string
): Validator<TOut, TransformDomain<TIn, TOut, D>> {
  return new TransformValidator(validator, transformFn, errorMessage);
}
```

### 2. TransformDomain<TIn, TOut>

A domain that wraps an inner domain and applies a transformation to generated values.

```typescript
// In packages/domain/src/domains/TransformDomain.ts

import { BaseDomain, Domain } from '../Domain';
import { DomainType } from '../types';

/**
 * Domain that transforms values from an inner domain.
 * 
 * Generation: generates from inner domain, then applies transform.
 * Contains: inverse check is not possible in general, so delegates to inner domain
 *           (this is a documented limitation - contains() may return false positives)
 */
export class TransformDomain<TIn, TOut, D extends Domain<TIn>> extends BaseDomain<TOut> {
  readonly kind = DomainType.TRANSFORM;
  
  constructor(
    public readonly inner: D,
    public readonly transform: (value: TIn) => TOut
  ) {
    super();
  }

  /**
   * Note: Cannot accurately check containment without inverse transform.
   * This returns true if the value could plausibly be in the output range.
   * For accurate validation, use the validator, not domain.contains().
   */
  contains(value: unknown): value is TOut {
    // Best effort: we can't invert the transform, so we can't check accurately
    // Return true to avoid false negatives; validation will catch actual errors
    return true;
  }
}

// Add to DomainType enum
export enum DomainType {
  // ... existing types
  TRANSFORM = 'transform',
}
```

### 3. TransformDomainGenerator

```typescript
// In packages/domain/src/generators/TransformDomainGenerator.ts

import { DomainGeneratorStrategy } from './DomainGeneratorStrategy';
import { TransformDomain } from '../domains/TransformDomain';
import { RNG } from './RNG';
import { DomainGeneratorStrategyRegistry } from './DomainGeneratorStrategyRegistry';

export class TransformDomainGenerator<TIn, TOut> 
  implements DomainGeneratorStrategy<TOut> {
  
  constructor(private readonly registry: DomainGeneratorStrategyRegistry) {}

  generate(domain: TransformDomain<TIn, TOut, any>, rng: RNG): TOut {
    // Generate from inner domain
    const innerValue = this.registry.generate(domain.inner, rng) as TIn;
    // Apply transform
    return domain.transform(innerValue);
  }
}
```

### 4. PipeValidator<TIn, TOut>

Chains two validators where the output of the first becomes the input to the second.

```typescript
/**
 * Pipes the output of one validator into another.
 * Useful for parsing: validate string, then validate parsed result.
 * 
 * @example
 * const jsonConfig = pipe(
 *   U(),                           // Validate it's a string
 *   transform(U(), s => JSON.parse(s)), // Parse JSON
 *   O({ port: I(), host: U() })    // Validate structure
 * );
 */
export class PipeValidator<TIn, TMid, TOut, DIn extends Domain<TIn>, DOut extends Domain<TOut>>
  extends BaseValidator<TOut, DOut> {
  
  public readonly domain: DOut;

  constructor(
    private readonly first: Validator<TIn, DIn>,
    private readonly transform: (value: TIn) => TMid,
    private readonly second: Validator<TOut, DOut>
  ) {
    super();
    this.domain = second.domain;
  }

  validate(value: unknown): ValidationResult<TOut> {
    // Validate with first
    const firstResult = this.first.validate(value);
    if (!firstResult.valid) {
      return firstResult as unknown as ValidationResult<TOut>;
    }

    // Transform
    let transformed: TMid;
    try {
      transformed = this.transform(firstResult.value);
    } catch (e) {
      return this.error(`Transform failed: ${e instanceof Error ? e.message : String(e)}`);
    }

    // Validate with second
    return this.second.validate(transformed);
  }
}

/**
 * Simple pipe that chains two validators directly (second validates first's output type).
 */
export function pipe<T, D1 extends Domain<T>, D2 extends Domain<T>>(
  first: Validator<T, D1>,
  second: Validator<T, D2>
): Validator<T, D2> {
  return new PipeValidator(first, x => x, second);
}
```

### 5. Fluent API Extension

```typescript
// Extend BaseValidator prototype
declare module '../../Validator' {
  interface BaseValidator<T, D extends Domain<T>> {
    /**
     * Transform the validated value.
     * @example U().transform(s => s.trim())
     */
    transform<TOut>(fn: (value: T) => TOut): Validator<TOut, TransformDomain<T, TOut, D>>;
    
    /**
     * Pipe output into another validator.
     * @example U().pipe(R(/^\d+$/))
     */
    pipe<D2 extends Domain<T>>(validator: Validator<T, D2>): Validator<T, D2>;
  }
}

BaseValidator.prototype.transform = function<T, TOut, D extends Domain<T>>(
  this: Validator<T, D>,
  fn: (value: T) => TOut
): Validator<TOut, TransformDomain<T, TOut, D>> {
  return new TransformValidator(this, fn);
};

BaseValidator.prototype.pipe = function<T, D1 extends Domain<T>, D2 extends Domain<T>>(
  this: Validator<T, D1>,
  validator: Validator<T, D2>
): Validator<T, D2> {
  return new PipeValidator(this, x => x, validator);
};
```

### 6. Common String Transforms (Convenience Methods)

```typescript
// Pre-built transforms for common string operations
declare module '../../Validator' {
  interface BaseValidator<T, D extends Domain<T>> {
    // Only available when T extends string
    trim(): T extends string ? Validator<string, TransformDomain<string, string, D>> : never;
    toLowerCase(): T extends string ? Validator<string, TransformDomain<string, string, D>> : never;
    toUpperCase(): T extends string ? Validator<string, TransformDomain<string, string, D>> : never;
  }
}

// Implementation (with runtime type check)
BaseValidator.prototype.trim = function(this: Validator<string, Domain<string>>) {
  return this.transform(s => s.trim());
};

BaseValidator.prototype.toLowerCase = function(this: Validator<string, Domain<string>>) {
  return this.transform(s => s.toLowerCase());
};

BaseValidator.prototype.toUpperCase = function(this: Validator<string, Domain<string>>) {
  return this.transform(s => s.toUpperCase());
};
```

## Usage Examples

```typescript
import { U, I, O, R, transform, pipe } from '@janus-validator/dsl';

// Basic transform
const trimmedName = U(1, 100).transform(s => s.trim());
trimmedName.validate("  Alice  "); // { valid: true, value: "Alice" }

// Convenience methods
const normalizedEmail = U(5, 100).trim().toLowerCase();
normalizedEmail.validate("  ALICE@Example.COM  "); 
// { valid: true, value: "alice@example.com" }

// Chained transforms
const slug = U(1, 100)
  .trim()
  .toLowerCase()
  .transform(s => s.replace(/\s+/g, '-'))
  .transform(s => s.replace(/[^a-z0-9-]/g, ''));

slug.validate("  Hello World! 123  ");
// { valid: true, value: "hello-world-123" }

// Type-changing transform (string → number)
const stringToInt = U().transform(s => parseInt(s, 10));
stringToInt.validate("42"); // { valid: true, value: 42 }

// Parsing JSON
const jsonConfig = U()
  .transform(s => JSON.parse(s) as { port: number; host: string })
  .pipe(O({ port: I(1, 65535), host: U(1, 255) }));

jsonConfig.validate('{"port": 3000, "host": "localhost"}');
// { valid: true, value: { port: 3000, host: "localhost" } }

// Transform with custom error
const parseDate = U().transform(
  s => {
    const d = new Date(s);
    if (isNaN(d.getTime())) throw new Error('Invalid date');
    return d;
  },
  'Please provide a valid date string'
);

// In object schemas
const User = O({
  name: U(1, 100).trim(),
  email: U(5, 100).trim().toLowerCase(),
  username: U(3, 20)
    .trim()
    .toLowerCase()
    .transform(s => s.replace(/\s+/g, '_')),
});

User.validate({
  name: "  Alice Smith  ",
  email: "  ALICE@EXAMPLE.COM  ",
  username: "  Alice Smith  ",
});
// {
//   valid: true,
//   value: {
//     name: "Alice Smith",
//     email: "alice@example.com",
//     username: "alice_smith",
//   }
// }

// Generation still works!
const generator = new Generator({ random: Math.random });
generator.generate(trimmedName.domain); 
// Generates a string from inner domain, then trims it
```

## Consequences

### Positive

1. **Enables parsing** - Can now validate AND transform in one pass
2. **Familiar API** - Matches Zod's `.transform()` that developers expect
3. **Type-safe** - Full inference: `U().transform(s => parseInt(s))` → `Validator<number>`
4. **Chainable** - Multiple transforms compose naturally
5. **Generation works** - TransformDomain generates then transforms
6. **Convenience methods** - `.trim()`, `.toLowerCase()` are common operations

### Negative

1. **Domain containment limitation** - `TransformDomain.contains()` cannot accurately check membership without inverse transform; returns `true` conservatively
2. **Non-invertible transforms** - Cannot "ungenerate" transformed values back to inputs
3. **Transform errors** - Runtime errors in transform functions become validation failures
4. **Type complexity** - Transform chains create nested `TransformDomain<TransformDomain<...>>` types

### Trade-offs

| Feature | Benefit | Cost |
|---------|---------|------|
| `contains()` returns true | No false negatives | May have false positives |
| Generate-then-transform | Generation works | May produce duplicates |
| Runtime type checks | Works with any validator | No compile-time enforcement of `.trim()` on strings |

## Implementation Notes

### Transform Error Handling

Transform functions that throw are caught and converted to validation errors:

```typescript
const risky = U().transform(s => {
  if (s.length > 10) throw new Error('Too long for processing');
  return s.toUpperCase();
});

risky.validate("this is too long");
// { valid: false, error: "Transform failed: Too long for processing" }
```

### Async Transforms (Future)

This ADR covers synchronous transforms only. Async transforms (`transformAsync`) are deferred to a future ADR on async validation.

## File Structure

```
packages/domain/src/
├── domains/
│   └── TransformDomain.ts      # TransformDomain class
├── generators/
│   └── TransformDomainGenerator.ts
└── types.ts                    # Add TRANSFORM to DomainType

packages/core/src/com/techlloyd/janus/
├── combinators/
│   ├── Transform.ts            # TransformValidator
│   ├── Pipe.ts                 # PipeValidator
│   └── modifiers/
│       └── stringTransforms.ts # trim, toLowerCase, toUpperCase
└── index.ts                    # Export transform, pipe
```

## Follow-ups

1. Consider `coerce()` modifier for automatic type coercion (string → number, etc.)
2. Add `preprocess()` for transforming input before validation (vs after)
3. Consider async transform support in future ADR
4. Add more string convenience methods: `.replace()`, `.slice()`, `.split()`
5. Consider numeric transforms: `.round()`, `.floor()`, `.ceil()`
