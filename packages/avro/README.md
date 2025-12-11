# @janus-validator/avro

Avro schema import/export for [Janus Validator](../core/README.md).

## Installation

```bash
npm install @janus-validator/avro @janus-validator/core
```

## Usage

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
      'x-janus-pattern': '^[\\w.]+@[\\w.]+\\.\\w+$'
    }
  ]
};

const validator = avroToValidator(avroSchema);

// Now you can validate data
validator.validate({ name: 'Alice', age: 30, email: 'alice@example.com' });
// { valid: true, value: { name: 'Alice', age: 30, email: 'alice@example.com' } }

// And generate test data
import { Generator } from '@janus-validator/core';
const generator = new Generator({ random: Math.random });
const testUser = generator.generate(validator);
```

### Export: Validator → Avro

Convert a Janus validator to an Avro schema:

```typescript
import { validatorToAvro } from '@janus-validator/avro';
import { O, S, I, R } from '@janus-validator/core/DSL';

const userValidator = O({
  name: S(1, 100),
  age: I(0, 150),
  email: R(/^[\w.]+@[\w.]+\.\w+$/),
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
//     { "name": "email", "type": "string", "x-janus-pattern": "^[\\w.]+@[\\w.]+\\.\\w+$" }
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
| `long` | `I(min?, max?)` |
| `float` | `N(min?, max?)` |
| `double` | `N(min?, max?)` |
| `string` | `S(minLen?, maxLen?)` or `R(pattern)` |
| `bytes` | `S(minLen?, maxLen?)` |
| `array` | `oneOrMore(item)` / `between(item, min, max)` |
| `record` | `O({ ... })` |
| `enum` | `Or(C('a'), C('b'), ...)` |
| `union` | `Or(type1, type2, ...)` |

## License

MIT

