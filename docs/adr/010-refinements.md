# ADR-010: Refinements via Composition

## Status
Accepted & Implemented

## Date
2026-01-08

## Context

Gap analysis against Zod revealed that janus-validator lacks custom validation predicates. Users cannot add business logic validation beyond what the built-in validators provide:

```typescript
// Zod allows custom predicates
const evenNumber = z.number().refine(n => n % 2 === 0, 'Must be even');
const password = z.string()
  .min(8)
  .refine(s => /[A-Z]/.test(s), 'Must contain uppercase')
  .refine(s => /[0-9]/.test(s), 'Must contain digit');

// Janus-validator cannot express this
const validator = I(0, 100); // No way to add "must be even"
```

Common refinement needs:
- **Numeric constraints**: even, odd, multiple of, positive, negative
- **String patterns**: contains, starts with, ends with
- **Cross-field validation**: password confirmation, date ranges
- **Business rules**: valid credit card, ISBN checksum

### Requirements

1. **`.refine(predicate, message)`** - Add custom validation predicate
2. **`.superRefine(check)`** - Complex validation with multiple issues
3. Support chaining multiple refinements
4. Provide clear error messages
5. Maintain type safety (refinements don't change type)
6. Document generation limitations

## Decision

Implement **RefineValidator** and **SuperRefineValidator** wrappers that add custom predicate checks after inner validation succeeds.

### 1. RefineValidator<T>

Simple predicate-based refinement.

```typescript
import { Validator, BaseValidator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { Domain } from '../Domain';

/**
 * Wrapper validator that adds a custom predicate check.
 * The refinement runs after the inner validator succeeds.
 * 
 * Note: Refinements do NOT affect the domain. Generated values may
 * fail refinement checks. Use refinements for business logic that
 * cannot be expressed as a domain constraint.
 */
export class RefineValidator<T, D extends Domain<T>> extends BaseValidator<T, D> {
  public readonly domain: D;

  constructor(
    private readonly inner: Validator<T, D>,
    private readonly predicate: (value: T) => boolean,
    private readonly message: string | ((value: T) => string),
    private readonly options?: {
      /** Abort early on first refinement failure (default: true) */
      abortEarly?: boolean;
      /** Custom error code for i18n */
      code?: string;
    }
  ) {
    super();
    // Domain is unchanged - refinements filter, they don't reshape
    this.domain = inner.domain;
  }

  validate(value: unknown): ValidationResult<T> {
    // First run inner validation
    const innerResult = this.inner.validate(value);
    if (!innerResult.valid) {
      return innerResult;
    }

    // Run refinement predicate
    const valid = this.predicate(innerResult.value);
    if (!valid) {
      const errorMsg = typeof this.message === 'function'
        ? this.message(innerResult.value)
        : this.message;
      
      // Use inner's error method to get an example
      return this.error(errorMsg);
    }

    return innerResult;
  }
}

/**
 * Adds a custom predicate check to a validator.
 * @param validator The inner validator
 * @param predicate Function that returns true if value is valid
 * @param message Error message or function that generates message
 * 
 * @example
 * const even = refine(I(0, 100), n => n % 2 === 0, 'Must be even');
 */
export function refine<T, D extends Domain<T>>(
  validator: Validator<T, D>,
  predicate: (value: T) => boolean,
  message: string | ((value: T) => string)
): Validator<T, D> {
  return new RefineValidator(validator, predicate, message);
}
```

### 2. SuperRefineValidator<T>

For complex validation with multiple issues or conditional logic.

```typescript
/**
 * Context passed to superRefine callbacks.
 */
export interface RefinementContext {
  /** Add a validation issue */
  addIssue: (issue: RefinementIssue) => void;
  /** Current path (for nested validation) */
  path: (string | number)[];
}

export interface RefinementIssue {
  message: string;
  code?: string;
  path?: (string | number)[];
}

/**
 * Wrapper validator for complex refinements that may produce multiple issues.
 */
export class SuperRefineValidator<T, D extends Domain<T>> extends BaseValidator<T, D> {
  public readonly domain: D;

  constructor(
    private readonly inner: Validator<T, D>,
    private readonly refinement: (value: T, ctx: RefinementContext) => void
  ) {
    super();
    this.domain = inner.domain;
  }

  validate(value: unknown): ValidationResult<T> {
    // First run inner validation
    const innerResult = this.inner.validate(value);
    if (!innerResult.valid) {
      return innerResult;
    }

    // Collect refinement issues
    const issues: RefinementIssue[] = [];
    const ctx: RefinementContext = {
      addIssue: (issue) => issues.push(issue),
      path: [],
    };

    this.refinement(innerResult.value, ctx);

    if (issues.length > 0) {
      // Combine issues into error message
      const errorMsg = issues
        .map(i => i.path?.length ? `${i.path.join('.')}: ${i.message}` : i.message)
        .join('; ');
      return this.error(errorMsg);
    }

    return innerResult;
  }
}

/**
 * Adds complex custom validation with multiple potential issues.
 * @param validator The inner validator
 * @param refinement Function that calls ctx.addIssue() for each problem
 * 
 * @example
 * const password = superRefine(U(8, 100), (value, ctx) => {
 *   if (!/[A-Z]/.test(value)) {
 *     ctx.addIssue({ message: 'Must contain uppercase letter' });
 *   }
 *   if (!/[0-9]/.test(value)) {
 *     ctx.addIssue({ message: 'Must contain digit' });
 *   }
 * });
 */
export function superRefine<T, D extends Domain<T>>(
  validator: Validator<T, D>,
  refinement: (value: T, ctx: RefinementContext) => void
): Validator<T, D> {
  return new SuperRefineValidator(validator, refinement);
}
```

### 3. Fluent API Extension

```typescript
declare module '../../Validator' {
  interface BaseValidator<T, D extends Domain<T>> {
    /**
     * Add a custom validation predicate.
     * @param predicate Function returning true if valid
     * @param message Error message (string or function)
     * 
     * @example
     * I(0, 100).refine(n => n % 2 === 0, 'Must be even')
     */
    refine(
      predicate: (value: T) => boolean,
      message?: string | ((value: T) => string)
    ): Validator<T, D>;

    /**
     * Add complex validation with multiple potential issues.
     * @param check Function that calls ctx.addIssue() for problems
     * 
     * @example
     * U(8, 100).superRefine((s, ctx) => {
     *   if (!/[A-Z]/.test(s)) ctx.addIssue({ message: 'Need uppercase' });
     *   if (!/[0-9]/.test(s)) ctx.addIssue({ message: 'Need digit' });
     * })
     */
    superRefine(check: (value: T, ctx: RefinementContext) => void): Validator<T, D>;
  }
}

BaseValidator.prototype.refine = function<T, D extends Domain<T>>(
  this: Validator<T, D>,
  predicate: (value: T) => boolean,
  message: string | ((value: T) => string) = 'Refinement failed'
): Validator<T, D> {
  return new RefineValidator(this, predicate, message);
};

BaseValidator.prototype.superRefine = function<T, D extends Domain<T>>(
  this: Validator<T, D>,
  check: (value: T, ctx: RefinementContext) => void
): Validator<T, D> {
  return new SuperRefineValidator(this, check);
};
```

### 4. Common Refinements (Convenience Methods)

Pre-built refinements for frequent use cases:

```typescript
// Numeric refinements
declare module '../../Validator' {
  interface BaseValidator<T, D extends Domain<T>> {
    // Available when T is number
    positive(message?: string): Validator<T, D>;
    negative(message?: string): Validator<T, D>;
    nonNegative(message?: string): Validator<T, D>;
    nonPositive(message?: string): Validator<T, D>;
    multipleOf(n: number, message?: string): Validator<T, D>;
    int(message?: string): Validator<T, D>;
    finite(message?: string): Validator<T, D>;
  }
}

// String refinements
declare module '../../Validator' {
  interface BaseValidator<T, D extends Domain<T>> {
    // Available when T is string
    email(message?: string): Validator<T, D>;
    url(message?: string): Validator<T, D>;
    uuid(message?: string): Validator<T, D>;
    cuid(message?: string): Validator<T, D>;
    startsWith(prefix: string, message?: string): Validator<T, D>;
    endsWith(suffix: string, message?: string): Validator<T, D>;
    includes(substring: string, message?: string): Validator<T, D>;
    regex(pattern: RegExp, message?: string): Validator<T, D>;
    nonempty(message?: string): Validator<T, D>;
  }
}

// Implementations
BaseValidator.prototype.positive = function(message = 'Must be positive') {
  return this.refine((n: number) => n > 0, message);
};

BaseValidator.prototype.multipleOf = function(n: number, message?: string) {
  return this.refine(
    (v: number) => v % n === 0,
    message ?? `Must be a multiple of ${n}`
  );
};

BaseValidator.prototype.email = function(message = 'Invalid email') {
  // Basic email regex - not RFC 5322 compliant but catches most cases
  return this.refine(
    (s: string) => /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(s),
    message
  );
};

BaseValidator.prototype.url = function(message = 'Invalid URL') {
  return this.refine((s: string) => {
    try {
      new URL(s);
      return true;
    } catch {
      return false;
    }
  }, message);
};

BaseValidator.prototype.uuid = function(message = 'Invalid UUID') {
  return this.refine(
    (s: string) => /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i.test(s),
    message
  );
};

BaseValidator.prototype.startsWith = function(prefix: string, message?: string) {
  return this.refine(
    (s: string) => s.startsWith(prefix),
    message ?? `Must start with "${prefix}"`
  );
};

BaseValidator.prototype.includes = function(substring: string, message?: string) {
  return this.refine(
    (s: string) => s.includes(substring),
    message ?? `Must include "${substring}"`
  );
};

BaseValidator.prototype.nonempty = function(message = 'Must not be empty') {
  return this.refine((s: string) => s.length > 0, message);
};
```

## Usage Examples

```typescript
import { U, I, N, O, refine, superRefine } from '@janus-validator/dsl';

// Simple predicate refinement
const evenNumber = I(0, 100).refine(n => n % 2 === 0, 'Must be even');
evenNumber.validate(4);  // { valid: true, value: 4 }
evenNumber.validate(5);  // { valid: false, error: 'Must be even' }

// Dynamic error message
const positiveBalance = N().refine(
  n => n > 0,
  n => `Balance must be positive, got ${n}`
);
positiveBalance.validate(-50);
// { valid: false, error: 'Balance must be positive, got -50' }

// Chained refinements
const password = U(8, 100)
  .refine(s => /[A-Z]/.test(s), 'Must contain uppercase letter')
  .refine(s => /[a-z]/.test(s), 'Must contain lowercase letter')
  .refine(s => /[0-9]/.test(s), 'Must contain digit')
  .refine(s => /[!@#$%^&*]/.test(s), 'Must contain special character');

// Complex validation with superRefine
const betterPassword = U(8, 100).superRefine((value, ctx) => {
  const issues = [];
  if (!/[A-Z]/.test(value)) issues.push('uppercase letter');
  if (!/[a-z]/.test(value)) issues.push('lowercase letter');
  if (!/[0-9]/.test(value)) issues.push('digit');
  if (!/[!@#$%^&*]/.test(value)) issues.push('special character');
  
  if (issues.length > 0) {
    ctx.addIssue({
      message: `Password must contain: ${issues.join(', ')}`,
    });
  }
});

// Convenience methods
const positiveInt = I().positive().int();
const userEmail = U(5, 100).email();
const websiteUrl = U(10, 2000).url();
const productCode = U(6, 6).startsWith('PRD-');

// In object schemas
const User = O({
  email: U(5, 100).email(),
  age: I(0, 150).positive(),
  website: U(10, 2000).url().optional(),
  referralCode: U(8, 8)
    .startsWith('REF-')
    .refine(s => /^REF-[A-Z0-9]{4}$/.test(s), 'Invalid referral code format'),
});

// Cross-field validation (at struct level)
const Registration = O({
  password: U(8, 100),
  confirmPassword: U(8, 100),
}).superRefine((value, ctx) => {
  if (value.password !== value.confirmPassword) {
    ctx.addIssue({
      message: 'Passwords must match',
      path: ['confirmPassword'],
    });
  }
});

// Date range validation
const DateRange = O({
  start: U(), // ISO date string
  end: U(),
}).superRefine((value, ctx) => {
  const start = new Date(value.start);
  const end = new Date(value.end);
  if (start >= end) {
    ctx.addIssue({
      message: 'End date must be after start date',
      path: ['end'],
    });
  }
});
```

## Consequences

### Positive

1. **Expressive** - Can add arbitrary business logic validation
2. **Chainable** - Multiple refinements compose naturally
3. **Good errors** - Dynamic messages provide context
4. **Familiar API** - Matches Zod's `.refine()` / `.superRefine()`
5. **Type-safe** - Refinements preserve input type
6. **Convenience methods** - Common patterns built-in

### Negative

1. **Generation limitation** - Refinements DO NOT affect domain; generated values may fail refinement
2. **No type narrowing** - Unlike Zod, `refine` doesn't narrow types (no branded types)
3. **Performance** - Each refinement adds a function call
4. **Order matters** - Refinements run in order; earlier failures prevent later checks

### Generation Limitation (Important)

**Refinements cannot affect value generation.** The domain remains unchanged, so `Generator.generate()` produces values that pass the inner validator but may fail refinements.

```typescript
const evenNumber = I(0, 100).refine(n => n % 2 === 0, 'Must be even');

const generator = new Generator({ random: Math.random });
const value = generator.generate(evenNumber.domain);
// May be 3, 17, 99, etc. - odd numbers are possible!

// For generation-safe validation, use domain-level constraints instead:
const evenDomain = new FiniteDomain([0, 2, 4, 6, 8, 10, ...]); // Explicit even values
```

**Recommendation:** Use refinements for validation-only business logic. For constraints that should affect generation, implement a custom domain.

## File Structure

```
packages/core/src/com/techlloyd/janus/
├── combinators/
│   ├── Refine.ts              # RefineValidator
│   ├── SuperRefine.ts         # SuperRefineValidator
│   └── refinements/
│       ├── index.ts           # Re-exports
│       ├── numeric.ts         # positive, negative, multipleOf, etc.
│       └── string.ts          # email, url, uuid, startsWith, etc.
└── index.ts                   # Export refine, superRefine
```

## Follow-ups

1. Consider `.brand<T>()` for type-level branding (compile-time only)
2. Add async refinement support (`refineAsync`) in future ADR
3. Consider refinement short-circuiting options (abort on first failure vs collect all)
4. Add more convenience refinements: IP address, phone number, credit card, etc.
5. Consider custom domain for common refinable patterns (e.g., `EvenIntegerDomain`)
