# ADR-008: Optional, Nullable, and Default Modifiers via Composition

## Status
Accepted & Implemented

## Date
2026-01-08

## Context

Gap analysis against Zod revealed that janus-validator lacks ergonomic modifiers for handling optional and nullable values. Currently, users must write verbose code:

```typescript
// Current approach - verbose
const optionalName = Or(U(1, 50), Undefined());
const nullableName = Or(U(1, 50), Null());
const nullishName = Or(U(1, 50), Null(), Undefined());
```

This is cumbersome compared to Zod's fluent API:

```typescript
// Zod approach - ergonomic
const optionalName = z.string().optional();
const nullableName = z.string().nullable();
const nullishName = z.string().nullish();
```

Additionally, there's no way to provide default values for missing fields, which is essential for configuration schemas and API responses.

### Requirements

1. **`.optional()`** - Accept `T | undefined`
2. **`.nullable()`** - Accept `T | null`
3. **`.nullish()`** - Accept `T | null | undefined`
4. **`.default(value)`** - Return default when input is `undefined`
5. Preserve full TypeScript type inference
6. Maintain domain-based generation capability
7. Follow composition pattern (wrap existing validators)

## Decision

Implement four **wrapper validators** that compose with any existing validator using the existing `AlternationDomain` infrastructure.

### 1. OptionalValidator<T>

Wraps a validator to also accept `undefined`.

```typescript
import { Validator, BaseValidator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { Domain, AlternationDomain, FiniteDomain } from '../Domain';

export class OptionalValidator<T, D extends Domain<T>> 
  extends BaseValidator<T | undefined, AlternationDomain<T | undefined>> {
  
  public readonly domain: AlternationDomain<T | undefined>;

  constructor(private readonly inner: Validator<T, D>) {
    super();
    this.domain = new AlternationDomain<T | undefined>([
      inner.domain as Domain<T | undefined>,
      new FiniteDomain([undefined]) as Domain<T | undefined>,
    ]);
  }

  validate(value: unknown): ValidationResult<T | undefined> {
    if (value === undefined) {
      return { valid: true, value: undefined };
    }
    return this.inner.validate(value) as ValidationResult<T | undefined>;
  }
}

/**
 * Makes a validator accept undefined in addition to its normal type.
 * @example
 * const maybeName = optional(U(1, 50)); // string | undefined
 */
export function optional<T, D extends Domain<T>>(
  validator: Validator<T, D>
): Validator<T | undefined, AlternationDomain<T | undefined>> {
  return new OptionalValidator(validator);
}
```

### 2. NullableValidator<T>

Wraps a validator to also accept `null`.

```typescript
export class NullableValidator<T, D extends Domain<T>> 
  extends BaseValidator<T | null, AlternationDomain<T | null>> {
  
  public readonly domain: AlternationDomain<T | null>;

  constructor(private readonly inner: Validator<T, D>) {
    super();
    this.domain = new AlternationDomain<T | null>([
      inner.domain as Domain<T | null>,
      new FiniteDomain([null]) as Domain<T | null>,
    ]);
  }

  validate(value: unknown): ValidationResult<T | null> {
    if (value === null) {
      return { valid: true, value: null };
    }
    return this.inner.validate(value) as ValidationResult<T | null>;
  }
}

/**
 * Makes a validator accept null in addition to its normal type.
 * @example
 * const nullableName = nullable(U(1, 50)); // string | null
 */
export function nullable<T, D extends Domain<T>>(
  validator: Validator<T, D>
): Validator<T | null, AlternationDomain<T | null>> {
  return new NullableValidator(validator);
}
```

### 3. NullishValidator<T>

Wraps a validator to accept both `null` and `undefined`.

```typescript
export class NullishValidator<T, D extends Domain<T>> 
  extends BaseValidator<T | null | undefined, AlternationDomain<T | null | undefined>> {
  
  public readonly domain: AlternationDomain<T | null | undefined>;

  constructor(private readonly inner: Validator<T, D>) {
    super();
    this.domain = new AlternationDomain<T | null | undefined>([
      inner.domain as Domain<T | null | undefined>,
      new FiniteDomain([null, undefined]) as Domain<T | null | undefined>,
    ]);
  }

  validate(value: unknown): ValidationResult<T | null | undefined> {
    if (value === null) {
      return { valid: true, value: null };
    }
    if (value === undefined) {
      return { valid: true, value: undefined };
    }
    return this.inner.validate(value) as ValidationResult<T | null | undefined>;
  }
}

/**
 * Makes a validator accept null or undefined in addition to its normal type.
 * @example
 * const nullishName = nullish(U(1, 50)); // string | null | undefined
 */
export function nullish<T, D extends Domain<T>>(
  validator: Validator<T, D>
): Validator<T | null | undefined, AlternationDomain<T | null | undefined>> {
  return new NullishValidator(validator);
}
```

### 4. DefaultValidator<T>

Wraps a validator to return a default value when input is `undefined`.

```typescript
export class DefaultValidator<T, D extends Domain<T>> extends BaseValidator<T, D> {
  public readonly domain: D;

  constructor(
    private readonly inner: Validator<T, D>,
    private readonly defaultValue: T | (() => T)
  ) {
    super();
    this.domain = inner.domain;
  }

  validate(value: unknown): ValidationResult<T> {
    if (value === undefined) {
      const resolved = typeof this.defaultValue === 'function'
        ? (this.defaultValue as () => T)()
        : this.defaultValue;
      return { valid: true, value: resolved };
    }
    return this.inner.validate(value);
  }
}

/**
 * Provides a default value when input is undefined.
 * @param validator The inner validator
 * @param value Default value or factory function
 * @example
 * const count = withDefault(I(0, 100), 0);
 * const timestamp = withDefault(I(), () => Date.now());
 */
export function withDefault<T, D extends Domain<T>>(
  validator: Validator<T, D>,
  value: T | (() => T)
): Validator<T, D> {
  return new DefaultValidator(validator, value);
}
```

### 5. Fluent API via Module Augmentation

To enable the familiar `.optional()` syntax, extend `BaseValidator`:

```typescript
// In core/src/com/techlloyd/janus/combinators/modifiers/index.ts

import { BaseValidator, Validator } from '../../Validator';
import { Domain, AlternationDomain } from '../../Domain';
import { OptionalValidator, NullableValidator, NullishValidator, DefaultValidator } from './validators';

// Extend BaseValidator prototype
BaseValidator.prototype.optional = function<T, D extends Domain<T>>(
  this: Validator<T, D>
): Validator<T | undefined, AlternationDomain<T | undefined>> {
  return new OptionalValidator(this);
};

BaseValidator.prototype.nullable = function<T, D extends Domain<T>>(
  this: Validator<T, D>
): Validator<T | null, AlternationDomain<T | null>> {
  return new NullableValidator(this);
};

BaseValidator.prototype.nullish = function<T, D extends Domain<T>>(
  this: Validator<T, D>
): Validator<T | null | undefined, AlternationDomain<T | null | undefined>> {
  return new NullishValidator(this);
};

BaseValidator.prototype.default = function<T, D extends Domain<T>>(
  this: Validator<T, D>,
  value: T | (() => T)
): Validator<T, D> {
  return new DefaultValidator(this, value);
};

// Type declarations
declare module '../../Validator' {
  interface BaseValidator<T, D extends Domain<T>> {
    optional(): Validator<T | undefined, AlternationDomain<T | undefined>>;
    nullable(): Validator<T | null, AlternationDomain<T | null>>;
    nullish(): Validator<T | null | undefined, AlternationDomain<T | null | undefined>>;
    default(value: T | (() => T)): Validator<T, D>;
  }
}
```

### DSL Integration

Add value modifier functions to the DSL. Note: The DSL already has an `optional()` function for array quantifiers (0 or 1 elements), so the optional value modifier is accessed via the fluent `.optional()` method only:

```typescript
// In dsl/src/com/techlloyd/janus/DSL.ts

// Re-export nullable, nullish, withDefault (not optional to avoid conflict)
export { nullable, nullish, withDefault } from '@janus-validator/core';

// For optional values, use the fluent method:
// U(1, 50).optional()   - creates string | undefined validator
// I(0, 100).default(0)  - provides default for undefined

// The existing DSL optional() is for array quantifiers:
// optional(I())  - creates number[] validator matching 0 or 1 elements
```

## Usage Examples

```typescript
import { U, I, B, O, Or, optional, nullable, withDefault } from '@janus-validator/dsl';

// Standalone function style (tree-shakeable)
const maybeName = optional(U(1, 50));
const nullableAge = nullable(I(0, 150));
const port = withDefault(I(1, 65535), 3000);

// Fluent method style (ergonomic)
const middleName = U(1, 50).optional();
const nickname = U(1, 20).nullable();
const theme = Or('light', 'dark').default('light');

// In object schemas
const Config = O({
  host: U(1, 255).default('localhost'),
  port: I(1, 65535).default(3000),
  debug: B().default(false),
  apiKey: U(10, 100).optional(),
  timeout: I(100, 30000).nullable(),
});

// Validation
Config.validate({});
// { valid: true, value: { host: 'localhost', port: 3000, debug: false } }

Config.validate({ apiKey: 'secret123', timeout: null });
// { valid: true, value: { host: 'localhost', port: 3000, debug: false, apiKey: 'secret123', timeout: null } }

// Generation still works
const generator = new Generator({ random: Math.random });
generator.generate(middleName.domain); // string | undefined
```

## Consequences

### Positive

1. **Familiar API** - Matches Zod's fluent interface developers expect
2. **Type-safe** - Full TypeScript inference: `U().optional()` → `Validator<string | undefined>`
3. **Composable** - Can chain: `U().optional().default('')`
4. **Generation-aware** - Domains correctly model the extended type space
5. **Tree-shakeable** - Standalone functions available for bundle optimization
6. **Backward compatible** - Existing `Or(validator, Null())` pattern still works

### Negative

1. **Prototype extension** - Unconventional but necessary for fluent API
2. **Import side-effects** - Must import modifiers module to enable prototype methods
3. **Chaining order matters** - `U().optional().default('')` vs `U().default('').optional()` have different semantics

### Migration

No breaking changes. Existing code using `Or(validator, Null())` continues to work. Users can gradually adopt the new modifiers.

## File Structure

```
packages/core/src/com/techlloyd/janus/
├── combinators/
│   ├── modifiers/
│   │   ├── index.ts           # Prototype extensions + re-exports
│   │   ├── Optional.ts        # OptionalValidator
│   │   ├── Nullable.ts        # NullableValidator
│   │   ├── Nullish.ts         # NullishValidator
│   │   └── Default.ts         # DefaultValidator
│   └── index.ts               # Add modifiers export
└── index.ts                   # Re-export modifiers

packages/dsl/src/com/techlloyd/janus/
└── DSL.ts                     # Add optional, nullable, nullish, withDefault
```

## Follow-ups

1. Update Struct validator to handle `.optional()` fields specially (don't require property to exist)
2. Consider `.required()` modifier to convert optional back to required
3. Add `.catch(fallback)` modifier for error recovery (similar to `.default()` but on validation failure)
4. Document chaining semantics clearly
