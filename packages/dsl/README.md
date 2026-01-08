# @janus-validator/dsl

Concise DSL for [Janus Validator](../core/README.md) - short aliases for all validators and combinators.

🚧 **Pre-1.0 notice:** This package has **not** reached `1.0` yet. Until then, the public API and behavior are **subject to change** between releases. If you need stability, **pin exact versions**.

The DSL is "just syntax": it builds validators from `@janus-validator/core`, so you still get:

- ✅ **Forward validation**: `validate(unknown)`
- 🎲 **Backwards generation**: `new Generator(rng).generate(validator)`

## Installation

```bash
npm install @janus-validator/dsl @janus-validator/core
```

## Quick Start

```typescript
import { B, U, S, I, N, L, R, O, Bytes, Or, Seq, oneOrMore } from '@janus-validator/dsl';
import { Generator } from '@janus-validator/core';

// Define validators with concise syntax
const userValidator = O({
  name: U(1, 100).trim(),                    // Trim whitespace
  age: I(0, 150).optional(),                 // Accept undefined
  email: R(/^[\w.]+@[\w.]+\.\w+$/)
    .message('Invalid email')                // Custom error message
    .code('INVALID_EMAIL'),                  // Error code for i18n
  active: B().default(true),                 // Default value
  role: Or('admin', 'user', 'guest'),        // Primitives auto-wrapped
});

// Validate data
const result = userValidator.validate({
  name: 'Alice',
  email: 'alice@example.com',
  role: 'admin',
});

// Generate test data
const generator = new Generator({ random: Math.random });
const testUser = generator.generate(userValidator.domain);
```

## Why this is powerful

The same validator definition can be used:
- In production (validate API requests / config / events)
- In tests (generate fixtures that must satisfy the same constraints)

```typescript
import { Generator } from '@janus-validator/core';
import { O, U, I } from '@janus-validator/dsl';

const User = O({ name: U(1, 50), age: I(0, 150) });
const generator = new Generator({ random: Math.random });

const fixture = generator.generate(User.domain);
const roundTrip = User.validate(fixture);
// roundTrip.valid === true
```

## DSL Reference

### Primitive Validators

| Function | Description | Example |
|----------|-------------|---------|
| `B()` | Boolean | `B()` |
| `U(min?, max?)` | Unicode string with length range | `U(1, 100)` |
| `S(...parts)` | Compound string from parts | `S(digits(4), '-', digits(2))` |
| `I(min?, max?)` | Integer in range | `I(0, 150)` |
| `N(min?, max?)` | Float in range | `N(-273.15, 1000)` |
| `L(min?, max?)` | 64-bit BigInt | `L(0n, 1000n)` |
| `R(pattern)` | Regex pattern | `R(/^\d{3}-\d{4}$/)` |
| `Bytes(min?, max?)` | Binary data (Uint8Array) | `Bytes(16, 32)` |

### Object & Special Values

| Function | Description | Example |
|----------|-------------|---------|
| `O(schema, strict?)` | Object/struct validator | `O({ name: U(), age: I() })` |
| `C(value)` | Constant value | `C(42)`, `C('hello')` |
| `Null()` | Matches `null` | `Null()` |
| `Undefined()` | Matches `undefined` | `Undefined()` |
| `Inf()` | Positive infinity | `Inf()` |
| `NInf()` | Negative infinity | `NInf()` |
| `NaN()` | Not-a-Number | `NaN()` |
| `Enum(enumObj)` | TypeScript enum | `Enum(Status)` |

### Combinators

| Function | Description | Example |
|----------|-------------|---------|
| `Or(...validators)` | Union/alternation | `Or(U(), I(), Null())` |
| `Seq(...validators)` | Tuple/sequence | `Seq(U(), I(), B())` |

### Character Sets (for `S()`)

| Function | Short | Description |
|----------|-------|-------------|
| `digits(n)` | `D(n)` | Digits (0-9) |
| `lower(n)` | | Lowercase (a-z) |
| `upper(n)` | | Uppercase (A-Z) |
| `letters(n)` | | Letters (a-zA-Z) |
| `alphanumeric(n)` | `A(n)` | Alphanumeric |
| `hex(n)` | `H(n)` | Hex (0-9a-f) |
| `hexUpper(n)` | | Hex (0-9A-F) |
| `chars(set, n)` | | Custom char set |

### Quantifiers (Arrays)

| Function | Description | Example |
|----------|-------------|---------|
| `zeroOrMore(v)` | 0+ elements | `zeroOrMore(I())` |
| `oneOrMore(v)` | 1+ elements | `oneOrMore(U())` |
| `optionalArray(v)` | 0 or 1 element array | `optionalArray(U())` |
| `exactly(v, n)` | Exactly n elements | `exactly(I(), 3)` |
| `atLeast(v, n)` | n+ elements | `atLeast(U(), 2)` |
| `between(v, min, max)` | min-max elements | `between(I(), 1, 5)` |

### Validator Modifiers (Fluent API)

| Method | Description | Example |
|--------|-------------|---------|
| `.optional()` | Accept `undefined` | `U(1, 50).optional()` |
| `.nullable()` | Accept `null` | `U(1, 50).nullable()` |
| `.nullish()` | Accept `null` or `undefined` | `U(1, 50).nullish()` |
| `.default(value)` | Default for `undefined` | `I(1, 100).default(50)` |
| `.transform(fn)` | Transform validated value | `U().transform(s => s.trim())` |
| `.trim()` | Trim whitespace (strings) | `U(1, 100).trim()` |
| `.toLowerCase()` | Lowercase (strings) | `U().toLowerCase()` |
| `.toUpperCase()` | Uppercase (strings) | `U().toUpperCase()` |
| `.refine(pred, msg)` | Add validation predicate | `I().refine(n => n > 0, 'positive')` |
| `.superRefine(fn)` | Complex validation | See examples below |
| `.message(msg)` | Custom error message | `I().message('Invalid age')` |
| `.code(code)` | Error code for i18n | `U().code('INVALID_EMAIL')` |
| `.describe(desc)` | Add description | `U().describe('User email')` |

### Type Assertion

```typescript
interface User { name: string; age: number; }

const userValidator = Typed<User>()(O({
  name: U(1, 100),
  age: I(0, 150),
}));
// Or use As<User>() as an alias
```

### String Modifiers

```typescript
// Case-insensitive matching
const hexColor = caseInsensitive(S('#', hex(6)));
hexColor.validate('#AABBCC'); // valid
hexColor.validate('#aabbcc'); // valid
```

## Recipes

### 1) Nested objects (strict vs non-strict)

```typescript
import { O, U, I } from '@janus-validator/dsl';

const User = O({
  name: U(1, 100),
  age: I(0, 150),
});

const StrictUser = O({ name: U(1, 100), age: I(0, 150) }, true);
```

### 2) "Enum-like" values (auto-wrapping)

```typescript
import { Or } from '@janus-validator/dsl';

const Status = Or('pending', 'active', 'complete');
// Type is: Validator<'pending' | 'active' | 'complete'>
```

### 3) Formatted strings without regex

```typescript
import { S, D, H } from '@janus-validator/dsl';

const ISODate = S(D(4), '-', D(2), '-', D(2));      // YYYY-MM-DD
const UUID = S(H(8), '-', H(4), '-', H(4), '-', H(4), '-', H(12));
```

### 4) Refinements and transforms

```typescript
import { O, U, I } from '@janus-validator/dsl';

const User = O({
  // Trim and lowercase email, then validate
  email: U(5, 100)
    .trim()
    .toLowerCase()
    .refine(s => s.includes('@'), 'Must be an email')
    .message('Please enter a valid email')
    .code('INVALID_EMAIL'),
  
  // Password with multiple requirements
  password: U(8, 100)
    .refine(s => /[A-Z]/.test(s), 'Need uppercase')
    .refine(s => /[0-9]/.test(s), 'Need digit'),
  
  // Optional field with default
  age: I(0, 150).optional(),
  verified: B().default(false),
});
```

### 5) Cross-field validation

```typescript
import { O, U } from '@janus-validator/dsl';

const SignupForm = O({
  password: U(8, 100),
  confirm: U(8, 100),
}).superRefine((value, ctx) => {
  if (value.password !== value.confirm) {
    ctx.addIssue({
      message: 'Passwords must match',
      path: ['confirm'],
    });
  }
});
```

### 6) Error handling

```typescript
import { O, U, I, flattenErrors, getErrorAtPath } from '@janus-validator/dsl';

const User = O({
  name: U(1, 50).message('Name is required'),
  email: U(5, 100)
    .refine(s => s.includes('@'))
    .code('INVALID_EMAIL'),
});

const result = User.validate({ name: '', email: 'bad' });

if (!result.valid) {
  // Flat array for form handling
  const errors = flattenErrors(result);
  // [{ path: 'name', message: 'Name is required' },
  //  { path: 'email', message: '...', code: 'INVALID_EMAIL' }]
  
  // Get specific field error
  const nameError = getErrorAtPath(result, 'name');
  if (nameError) setFieldError('name', nameError.message);
}
```

## Auto-Wrapping

The `Or`, `Seq`, and `O` combinators automatically wrap primitive values and enums:

```typescript
// Primitives auto-wrapped in Constant
const protocol = Or('http', 'https', 'ws');  // No need for C()
const config = O({ version: 1, env: 'prod' });

// Enums auto-wrapped
enum Status { Active = 'active', Inactive = 'inactive' }
const task = O({
  status: Status,  // Automatically creates Or('active', 'inactive')
});
```

## Error Formatting Utilities

```typescript
import {
  flattenErrors,    // Get all errors as flat array
  formatErrors,     // Human-readable string  
  errorsToJson,     // JSON for API responses
  getFirstError,    // Get first error only
  getErrorAtPath,   // Find error at specific path
  getErrorsByPath,  // Group errors by path
} from '@janus-validator/dsl';
```

## License

MIT
