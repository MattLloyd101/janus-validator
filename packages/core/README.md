# @janus-validator/core

Core validation library for Janus Validator - composable validators that can both **validate data** and **generate valid examples**. Perfect for testing, API validation, and form handling.

## Features

- 🎯 **Type-safe validation** with clear, helpful error messages
- 🎲 **Automatic test data generation** from validator definitions
- 🧩 **Composable validators** for complex schemas
- 📝 **Concise DSL** available [@janus-validator/dsl](../dsl/README.md)
- ✨ **Auto-wrapping** - Primitives in `Or`, `Seq`, and `O` are automatically wrapped in `Constant`
- 🎭 **Realistic presets** for names, emails, addresses, etc.
- 🔧 **Custom generators** to override default generation

## Installation

```bash
# Core + DSL package (recommended)
npm install @janus-validator/core @janus-validator/dsl

# Or just core (DSL available via @janus-validator/core/DSL)
npm install @janus-validator/core
```

## Quick Start

```typescript
// Option 1: Import from DSL package
import { O, U, I, B, R, Or, oneOrMore } from '@janus-validator/dsl';

import { Generator } from '@janus-validator/core';

// Define a validator
const userValidator = O({
  name: S(1, 100),
  age: I(0, 150),
  email: R(/^[\w.]+@[\w.]+\.\w+$/),
  active: B(),
});

// Validate data
const result = userValidator.validate({
  name: 'Alice',
  age: 30,
  email: 'alice@example.com',
  active: true,
});

if (result.valid) {
  console.log('Valid:', result.value);
} else {
  console.log('Error:', result.error);
  console.log('Example:', result.example); // Auto-generated valid example
}

// Generate test data
const generator = new Generator({ random: Math.random });
const testUser = generator.generate(userValidator);
// { name: 'Alice', age: 42, email: 'test@example.com', active: true }
```

## DSL Reference

### Primitive Validators

| Function | Description | Example |
|----------|-------------|---------|
| `B()` | Boolean | `B()` |
| `S(min?, max?)` | String with length range | `S(1, 100)` |
| `I(min?, max?)` | Integer in range | `I(0, 150)` |
| `N(min?, max?)` | Float in range | `N(-273.15, 1000)` |
| `L(min?, max?)` | 64-bit BigInt | `L(0n, 1000n)` |
| `R(pattern)` | Regex pattern | `R(/^\d{3}-\d{4}$/)` |
| `Bytes(min?, max?)` | Binary data (Uint8Array) | `Bytes(16, 32)` |

### Object & Struct

```typescript
// Object schema - primitives are auto-wrapped in Constant
const config = O({
  version: 1,               // Auto-wrapped: C(1)
  env: 'production',        // Auto-wrapped: C('production')
  debug: false,             // Auto-wrapped: C(false)
  port: I(1, 65535),        // Validator passed through
});

// Nested objects
const user = O({
  name: S(1, 50),
  age: I(0, 150),
  address: O({
    street: S(1, 200),
    city: S(1, 100),
    zip: R(/^\d{5}$/),
  }),
});
```

### Special Values

| Function | Description |
|----------|-------------|
| `Null()` | Matches `null` |
| `Undefined()` | Matches `undefined` |
| `C(value)` | Constant value |
| `Enum(enumObj)` | TypeScript enum |
| `Inf()` | Positive infinity |
| `NInf()` | Negative infinity |
| `NaN()` | Not-a-Number |

### Auto-Wrapping Primitives

The `Or`, `Seq`, and `O` combinators automatically wrap primitive values (strings, numbers, booleans) in `Constant` validators. This makes schemas more concise:

```typescript
// Before: explicit wrapping required
const status = Or(C('pending'), C('active'), C('completed'));
const config = O({ version: C(1), env: C('production') });

// After: primitives auto-wrapped
const status = Or('pending', 'active', 'completed');
const config = O({ version: 1, env: 'production' });
```


### TypeScript Enums

Use `Enum()` to create a validator directly from a TypeScript enum:

```typescript
import { Enum, O, S } from '@janus-validator/core/DSL';

// String enum
enum Status {
  Pending = 'pending',
  Active = 'active',
  Completed = 'completed',
}

const statusValidator = Enum(Status);
// Equivalent to: Or('pending', 'active', 'completed')

statusValidator.validate('pending');   // ✓
statusValidator.validate('invalid');   // ✗

// Numeric enum
enum Direction { Up, Down, Left, Right }
const dirValidator = Enum(Direction);  // Or(0, 1, 2, 3)

// Use in object schemas
const task = O({
  name: S(1, 100),
  status: Enum(Status),
});
```

### Combinators

#### Union Types (Or)

```typescript
// String or number - type is automatically inferred as Validator<string | number>
const id = Or(S(10, 36), I(1, 1000000));

// Nullable string - type is Validator<string | null>
const optionalName = Or(S(1, 100), Null());

// Enum-like constants - primitives auto-wrapped!
const status = Or('pending', 'active', 'completed');
// Type: Validator<'pending' | 'active' | 'completed'>

// Mix validators and primitives
const responseCode = Or(200, 201, 204, 404, 500);
// Type: Validator<200 | 201 | 204 | 404 | 500>

const flexible = Or('auto', I(1, 100));
// Type: Validator<'auto' | number>
```

#### Arrays (Quantifiers)

```typescript
// One or more items
const tags = oneOrMore(S(1, 20));

// Zero or more items
const comments = zeroOrMore(S(1, 500));

// Optional (0 or 1)
const nickname = optional(S(1, 30));

// Exactly N items
const coordinates = exactly(N(), 2);

// Between min and max
const scores = between(I(0, 100), 1, 5);

// At least N items
const required = atLeast(S(), 3);
```

#### Tuples (Sequence)

```typescript
// Fixed-length heterogeneous array with automatic tuple type inference
const point = Seq(N(), N());           // Validator<[number, number]>
const person = Seq(S(), I(), B());     // Validator<[string, number, boolean]>

// Primitives are auto-wrapped!
const header = Seq('START', I(), 'END');
// Type: Validator<['START', number, 'END']>

const record = Seq(1, S(1, 10), true);
// Type: Validator<[1, string, true]>

// Types are properly inferred in results
const result = person.validate(['Alice', 30, true]);
if (result.valid) {
  const [name, age, active] = result.value; // name: string, age: number, active: boolean
}
```

### Type Assertion

Use `Typed<T>()` or `As<T>()` to explicitly assert the output type of a validator, perfect for integrating with your existing interfaces:

```typescript
import { O, S, I, Typed, As } from '@janus-validator/core/DSL';

// Define your interfaces
interface User {
  name: string;
  age: number;
}

interface Address {
  street: string;
  city: string;
}

// Create typed validators
const AddressValidator = Typed<Address>()(O({
  street: S(1, 200),
  city: S(1, 100),
}));

// As is an alias for Typed. Does not cast, 
// but typechecks that the object matches the interface.
const UserValidator = As<User>()(O({
  name: S(1, 100),
  age: I(0, 150),
}));

// Result is properly typed
const result = UserValidator.validate({ name: 'Alice', age: 30 });
if (result.valid) {
  const user: User = result.value; // No casting needed!
}
```

### Binary Data

Validate `Uint8Array` or `Buffer` data with length constraints:

```typescript
import { Bytes } from '@janus-validator/core/DSL';

// Variable length binary (0-1024 bytes)
const data = Bytes();

// Fixed length (exactly 16 bytes, e.g., UUID)
const uuid = Bytes(16, 16);

// Range (32-64 bytes)
const hash = Bytes(32, 64);
```

### BigInt / Long

For 64-bit integers that exceed JavaScript's `Number.MAX_SAFE_INTEGER`:

```typescript
import { L } from '@janus-validator/core/DSL';

// Default: full 64-bit signed range
const bigId = L();

// Custom range
const positiveId = L(0n, 1000000000000n);

// Accepts bigint, number (if safe), or string representation
bigId.validate(9007199254740993n);  // ✓
bigId.validate('9007199254740993'); // ✓ (auto-converted)
```

### Capture & Reference

For validating matching values (like password confirmation):

```typescript
const { capture, ref, context } = createCaptureGroup();

const registrationForm = O({
  password: capture('pwd', S(8, 100)),
  confirmPassword: ref('pwd'),
});

// Valid: passwords match
registrationForm.validate({
  password: 'secret123',
  confirmPassword: 'secret123',
}); // { valid: true }

// Invalid: passwords don't match
registrationForm.validate({
  password: 'secret123',
  confirmPassword: 'different',
}); // { valid: false, error: "Value does not match captured 'pwd'" }
```

## Realistic Data Presets

Generate realistic test data:

```typescript
import {
  FirstName, LastName, FullName,
  RealisticEmail, CorporateEmailPreset,
  RealisticUSPhone,
  RealisticStreetAddress, RealisticCity, RealisticState, RealisticZipCode,
  CompanyName, ProductName,
  RecentDate, FutureDate,
  RealisticPrice,
} from '@janus-validator/core/lib';

const customer = O({
  name: FullName(),           // "Alice Smith"
  email: RealisticEmail(),    // "alice.smith@gmail.com"
  phone: RealisticUSPhone(),  // "(555) 123-4567"
  address: O({
    street: RealisticStreetAddress(), // "1234 Oak St"
    city: RealisticCity(),            // "New York"
    state: RealisticState(),          // "NY"
    zip: RealisticZipCode(),          // "10001"
  }),
});

const testCustomer = generator.generate(customer);
```

## Custom Generators

Override default generation with custom logic:

```typescript
import { fromValues, templateGenerator, withGenerator } from '@janus-validator/core/combinators';

// Generate from a fixed list
const country = fromValues(R(/^[A-Z]{2}$/), ['US', 'CA', 'GB', 'DE', 'FR']);

// Template-based generation
const sku = templateGenerator(S(10, 20), (pick, rng) => {
  const categories = ['ELEC', 'FURN', 'CLTH'];
  const num = Math.floor(rng.random() * 10000).toString().padStart(4, '0');
  return `${pick(categories)}-${num}`;
});
// Generates: "ELEC-0042", "FURN-1337", etc.

// Custom generation function
const userId = withGenerator(I(1, 1000000), (rng) => {
  return Math.floor(rng.random() * 1000000) + 1;
});
```

## Error Messages with Examples

All DSL validators automatically include valid examples in error messages:

```typescript
const age = I(18, 100);
const result = age.validate('not a number');

// result = {
//   valid: false,
//   error: 'Expected number, got string',
//   example: 42  // Auto-generated valid example
// }
```

## Real-World Examples

### API Request Validation

```typescript
const createUserRequest = O({
  username: R(/^[a-zA-Z][a-zA-Z0-9_]{2,19}$/),
  email: R(/^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$/),
  password: S(8, 128),
  profile: O({
    firstName: S(1, 50),
    lastName: S(1, 50),
    age: Or(I(13, 150), Null()),
  }),
});

// In your API handler
const result = createUserRequest.validate(req.body);
if (!result.valid) {
  return res.status(400).json({ error: result.error });
}
```

### Form Validation

```typescript
const { capture, ref, context } = createCaptureGroup();

const signupForm = O({
  email: R(/^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$/),
  password: capture('pwd', S(8, 100)),
  confirmPassword: ref('pwd'),
  acceptTerms: true, // Must be true (auto-wrapped)
});

function validateForm(data: unknown) {
  context.clear();
  return signupForm.validate(data);
}
```

### E-Commerce Order

```typescript
const orderItem = O({
  productId: S(10, 50),
  name: S(1, 200),
  quantity: I(1, 100),
  unitPrice: N(0.01, 100000),
});

const order = O({
  orderId: R(/^ORD-\d{8}$/),
  customerId: I(1, 1000000),
  items: oneOrMore(orderItem),
  subtotal: N(0, 1000000),
  tax: N(0, 100000),
  total: N(0, 1100000),
  status: Or('pending', 'processing', 'shipped', 'delivered'), // Auto-wrapped!
  createdAt: R(/^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}/),
});
```

### Test Data Generation

```typescript
import { Generator } from '@janus-validator/core';

const rng = { random: Math.random };
const generator = new Generator(rng);

// Generate 100 test users
const testUsers = Array.from({ length: 100 }, () => 
  generator.generate(userValidator)
);

// Use in tests
describe('UserService', () => {
  it('should create users', () => {
    const user = generator.generate(userValidator);
    const created = userService.create(user);
    expect(created.id).toBeDefined();
  });
});
```

## API Reference

### Validator Interface

```typescript
interface Validator<T> {
  validate(input: unknown): ValidationResult<T>;
  domain: Domain<T>;
}

type ValidationResult<T> =
  | { valid: true; value: T }
  | { valid: false; error: string; example?: T };
```

### Type Utilities

Helper types for working with validators:

```typescript
import {
  InferValidatorType,   // Extract T from Validator<T>
  UnionOfValidators,    // [Validator<A>, Validator<B>] => A | B
  TupleOfValidators,    // [Validator<A>, Validator<B>] => [A, B]
  ValidatorSchema,      // { [key: string]: Validator<any> }
  InferSchemaType,      // { a: Validator<A> } => { a: A }
} from '@janus-validator/core';

// Example: Infer type from any validator
type UserType = InferValidatorType<typeof userValidator>;
```

### Generator Class

```typescript
class Generator {
  constructor(rng: RNG);
  generate<T>(validator: Validator<T>): T;
}

interface RNG {
  random(): number; // Returns 0-1
}
```

## License

MIT
