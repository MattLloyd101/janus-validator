# Janus Validator

A TypeScript combinator library for defining validators that can both **validate data** and **generate valid examples**.

🚧 **Pre-1.0 notice:** This project has **not** reached `1.0` yet. Until then, the public API and behavior are **subject to change** between releases. If you need stability, **pin exact versions**.

Janus is built around a simple idea:

- **Validate forwards**: check unknown input and get back a typed value (or a structured error)
- **Run “backwards”**: generate values that *must* satisfy the same validator (great for tests and fixtures)

## Features

- 🧩 **Composable validators** - Build complex schemas from small parts
- 🎲 **Automatic data generation** - Generate valid examples from any validator
- 🧬 **Structured errors** - Errors can mirror the shape of your input with per-field/per-index results
- 📝 **Concise DSL** - Short aliases for quick definitions
- 🎯 **Type inference** - Union types (`Or`), tuple types (`Seq`), and object shapes are inferred

## Packages

| Package | Description |
|---------|-------------|
| [@janus-validator/core](./packages/core/README.md) | Core validation library with generators |
| [@janus-validator/dsl](./packages/dsl/README.md) | Concise DSL with short aliases |
| [@janus-validator/avro](./packages/avro/README.md) | Avro schema import/export |

## Installation

```bash
# Core library with DSL
npm install @janus-validator/core @janus-validator/dsl

# Or just core (no DSL)
npm install @janus-validator/core

# With Avro support
npm install @janus-validator/core @janus-validator/dsl @janus-validator/avro
```

## Quick Start

```typescript
import { O, U, I, B, R, Or, Typed } from '@janus-validator/dsl';

import { Generator } from '@janus-validator/core';

// Define a validator with automatic type inference
// Primitives are auto-wrapped in Constant validators
const userValidator = O({
  name: U(1, 100),
  age: I(0, 150),
  email: R(/^[\w.]+@[\w.]+\.\w+$/),
  active: B(),
  role: Or('admin', 'user', 'guest'),  // Primitives auto-wrapped!
  version: 1,                           // Also auto-wrapped
});

// Validate data
const result = userValidator.validate({
  name: 'Alice',
  age: 30,
  email: 'alice@example.com',
  active: true,
  role: 'admin',
  version: 1,
});

// Generate test data
const generator = new Generator({ random: Math.random });
const testUser = generator.generate(userValidator.domain);

// Type assertion for interfaces
interface User { name: string; age: number; }
const TypedUserValidator = Typed<User>()(O({ name: U(1, 100), age: I(0, 150) }));
```

## The “two faces”: validate + generate

The same validator definition supports both directions:

```typescript
import { Generator } from '@janus-validator/core';
import { O, U, I, B, Or, Null } from '@janus-validator/dsl';

const User = O({
  name: U(1, 50),
  age: I(0, 150),
  active: B(),
  nickname: Or(U(1, 30), Null()),
});

// Backwards: generate fixtures
const generator = new Generator({ random: Math.random });
const fixture = generator.generate(User.domain);

// Forwards: validate runtime input (fixtures always validate)
const roundTrip = User.validate(fixture);
// roundTrip.valid === true
```

## Structured errors (and examples)

Errors include:
- `error`: a human readable message
- `path` / `pathString`: exact location of the error (e.g., `['user', 'email']` → `'user.email'`)
- `code`: optional error code for i18n
- `results`: recursive per-field/per-element results
- `example`: a generated value that would pass the validator

```typescript
import { O, U, I, flattenErrors } from '@janus-validator/dsl';

const Profile = O({ name: U(1, 50), age: I(0, 150) });
const result = Profile.validate({ name: 'Alice', age: 999 });

if (!result.valid) {
  result.error;      // "age: Expected value <= 150, got 999"
  result.example;    // auto-generated valid example
  result.results;    // per-field results (recursive)
  
  // Flatten all errors for form handling
  const errors = flattenErrors(result);
  // [{ path: 'age', message: '...', code: undefined }]
}
```

## Modifiers (optional, transforms, refinements)

Chain modifiers for common patterns:

```typescript
import { O, U, I, B } from '@janus-validator/dsl';

const User = O({
  name: U(1, 50).trim(),                    // Trim whitespace
  email: U(5, 100)
    .trim()
    .toLowerCase()
    .refine(s => s.includes('@'), 'Invalid email')
    .message('Please enter a valid email')  // Custom error message
    .code('INVALID_EMAIL'),                 // Error code for i18n
  age: I(0, 150).optional(),                // T | undefined
  nickname: U(1, 20).nullable(),            // T | null
  verified: B().default(false),             // Default value
});
```

See the [DSL package README](./packages/dsl/README.md) for the full DSL reference.

## Development

```bash
# Install dependencies
npm install

# Build all packages
npm run build

# Run all tests
npm test

# Build/test specific package
npm run build --workspace=@janus-validator/core
npm run test --workspace=@janus-validator/core

```

## Why Janus?

Janus is a Roman God of beginnings, transitions and passages. He is depicted with two faces, one looking towards the past and another towards the future.

Similarly this library has two core aspects, validation and generation. That's about it 🤷‍♂️

## License

MIT
