# Janus Validator

A TypeScript combinator library for defining validators that can both **validate data** and **generate valid examples**.

## Features

- 🧩 **Composable validators** - Build complex schemas from simple primitives
- 🎲 **Automatic test data generation** - Generate valid examples from any validator
- 📝 **Concise DSL** - Short aliases for quick definitions
- 🎯 **Full type inference** - Union types (`Or`), tuple types (`Seq`), and object shapes are automatically inferred

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

# Or just core (DSL also available via @janus-validator/core/DSL)
npm install @janus-validator/core

# With Avro support
npm install @janus-validator/core @janus-validator/dsl @janus-validator/avro
```

## Quick Start

```typescript
// Option 1: Import from dedicated DSL package
import { O, U, I, B, R, Or, Typed } from '@janus-validator/dsl';

// Option 2: Import from core
import { O, U, I, B, R, Or, Typed } from '@janus-validator/core/DSL';

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
const testUser = generator.generate(userValidator);

// Type assertion for interfaces
interface User { name: string; age: number; }
const TypedUserValidator = Typed<User>()(O({ name: U(1, 100), age: I(0, 150) }));
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
