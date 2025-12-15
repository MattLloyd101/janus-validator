# @janus-validator/avro

Avro schema import/export for [Janus Validator](../core/README.md).

🚧 **Pre-1.0 notice:** This package has **not** reached `1.0` yet. Until then, the public API and behavior are **subject to change** between releases. If you need stability, **pin exact versions**.

## Installation

```bash
npm install @janus-validator/avro @janus-validator/core
```

## Usage

**Status:**
- ✅ `avroToValidator()` - Implemented
- 🚧 `validatorToAvro()` - Not yet implemented (throws `Error('Not yet implemented')`)

## Why this package exists

Avro schemas describe *shape* but don’t standardize validation constraints (lengths, numeric bounds, regex patterns, etc).
This package is intended to bridge that gap by encoding validation constraints as `x-janus-*` extension fields, so the
same schema can be:

- **Validated forwards** (Avro → Janus validator → validate)
- **Generated backwards** (Janus validator → Generator → fixtures)

### Import: Avro → Validator

Convert an Avro schema to a Janus validator:

```typescript
import { avroToValidator } from '@janus-validator/avro';

const avroSchema = {
  type: 'record',
  name: 'User',
  fields: [
    {
      name: 'name',
      type: 'string',
      'x-janus-minLength': 1,
      'x-janus-maxLength': 100
    },
    {
      name: 'age',
      type: 'int',
      'x-janus-min': 0,
      'x-janus-max': 150
    },
    {
      name: 'email',
      type: 'string',
      'x-janus-pattern': '^[A-Za-z0-9_.]+@[A-Za-z0-9_.]+\\.[A-Za-z0-9_]+$'
    }
  ]
};

const validator = avroToValidator(avroSchema);

validator.validate({ name: 'Alice', age: 30, email: 'alice@example.com' }); // { valid: true }

// And generate test data
import { Generator } from '@janus-validator/core';
const generator = new Generator({ random: Math.random });
const testUser = generator.generate(validator.domain);
```

### Export: Validator → Avro

Convert a Janus validator to an Avro schema:

```typescript
import { validatorToAvro } from '@janus-validator/avro';
import { O, U, I, R } from '@janus-validator/dsl';

const userValidator = O({
  name: U(1, 100),
  age: I(0, 150),
  email: R(/^[A-Za-z0-9_.]+@[A-Za-z0-9_.]+\.[A-Za-z0-9_]+$/),
});

const schema = validatorToAvro(userValidator, {
  name: 'User',
  namespace: 'com.example',
  includeExtensions: true
});

console.log(JSON.stringify(schema, null, 2));
// {
//   "type": "record",
//   "name": "User",
//   "namespace": "com.example",
//   "fields": [
//     { "name": "name", "type": "string", "x-janus-minLength": 1, "x-janus-maxLength": 100 },
//     { "name": "age", "type": "int", "x-janus-min": 0, "x-janus-max": 150 },
//     { "name": "email", "type": "string", "x-janus-pattern": "^[A-Za-z0-9_.]+@[A-Za-z0-9_.]+\\.[A-Za-z0-9_]+$" }
//   ]
// }
```

## Extended Schema Fields

Since Avro doesn't natively support validation constraints, this package uses `x-janus-*` prefixed fields:

| Field | Type | Description |
|-------|------|-------------|
| `x-janus-min` | `number` | Minimum value for numeric types |
| `x-janus-max` | `number` | Maximum value for numeric types |
| `x-janus-minLength` | `number` | Minimum length for string/bytes |
| `x-janus-maxLength` | `number` | Maximum length for string/bytes |
| `x-janus-pattern` | `string` | Regex pattern for strings |
| `x-janus-enum` | `unknown[]` | Allowed constant values |
| `x-janus-minItems` | `number` | Minimum array length |
| `x-janus-maxItems` | `number` | Maximum array length |
| `x-janus-description` | `string` | Human-readable description |
| `x-janus-examples` | `unknown[]` | Example values for generation |

## Type Mapping

| Avro Type | Janus Validator |
|-----------|-----------------|
| `null` | `Null()` |
| `boolean` | `B()` |
| `int` | `I(min?, max?)` |
| `long` | `L(min?, max?)` |
| `float` | `N(min?, max?)` |
| `double` | `N(min?, max?)` |
| `string` | `U(minLen?, maxLen?)` or `R(pattern)` |
| `bytes` | `Bytes(minLen?, maxLen?)` |
| `array` | `oneOrMore(item)` / `between(item, min, max)` |
| `record` | `O({ ... })` |
| `enum` | `Or('a', 'b', ...)` |
| `union` | `Or(type1, type2, ...)` |

## Roadmap

Planned behavior once implemented:
- `avroToValidator(schema)`:
  - Produces a validator from Avro schema + `x-janus-*` constraints
  - Records become `Struct(...)` / DSL `O(...)` with configurable strictness
- `validatorToAvro(validator)`:
  - Encodes domains/constraints back into Avro types + `x-janus-*` fields

## License

MIT

