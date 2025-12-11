# @janus-validator/dsl

Concise DSL for [Janus Validator](../core/README.md) - short aliases for all validators and combinators.

## Installation

```bash
npm install @janus-validator/dsl @janus-validator/core
```

## Quick Start

```typescript
import { B, S, I, N, L, R, O, Bytes, Or, Seq, optional, oneOrMore } from '@janus-validator/dsl';
import { Generator } from '@janus-validator/core';

// Define validators with concise syntax
const userValidator = O({
  name: U(1, 100),
  age: I(0, 150),
  email: R(/^[\w.]+@[\w.]+\.\w+$/),
  active: B(),
  role: Or('admin', 'user', 'guest'),  // Primitives auto-wrapped
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

### Quantifiers

| Function | Description | Example |
|----------|-------------|---------|
| `zeroOrMore(v)` | 0+ elements | `zeroOrMore(I())` |
| `oneOrMore(v)` | 1+ elements | `oneOrMore(U())` |
| `optional(v)` | 0 or 1 element | `optional(U())` |
| `exactly(v, n)` | Exactly n elements | `exactly(I(), 3)` |
| `atLeast(v, n)` | n+ elements | `atLeast(U(), 2)` |
| `between(v, min, max)` | min-max elements | `between(I(), 1, 5)` |

### Type Assertion

```typescript
interface User { name: string; age: number; }

const userValidator = Typed<User>()(O({
  name: U(1, 100),
  age: I(0, 150),
}));
// Or use As<User>() as an alias
```

### Capture & Reference

```typescript
const { capture, ref, context } = createCaptureGroup();

const form = O({
  password: capture('pwd', U(8, 100)),
  confirmPassword: ref('pwd'),
});
```

### String Modifiers

```typescript
// Case-insensitive matching
const hexColor = caseInsensitive(S('#', hex(6)));
hexColor.validate('#AABBCC'); // valid
hexColor.validate('#aabbcc'); // valid
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

## License

MIT

