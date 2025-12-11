# ADR-001: Avro Map Type Handling

## Status

Accepted

## Date

2024-12-11

## Context

Avro schemas support a `map` type that represents a dictionary with string keys and homogeneous values:

```json
{
  "type": "map",
  "values": "int"
}
```

This would accept objects like `{ "key1": 42, "key2": 100 }` where all values are integers.

Janus Validator has a `Struct` combinator for validating objects with known schemas:

```typescript
Struct({ name: S(), age: I() })
```

The question arose whether we need a dedicated `Map` combinator to support Avro's map type, or whether existing combinators are sufficient.

### Analysis

| Feature | `Struct` (non-strict) | Hypothetical `Map` |
|---------|----------------------|-------------------|
| Known keys with types | ✅ | ❌ |
| Arbitrary string keys | ✅ (ignores extras) | ✅ |
| Validate all values uniformly | ❌ | ✅ |
| Use case | Defined schemas | Dynamic dictionaries |

The key difference: `Struct({})` accepts any object but does **not** validate the values of unknown keys. A true `Map(validator)` would validate that every value passes the inner validator.

### Considerations

1. **Complexity vs. Utility**: Adding a Map combinator increases library complexity for a use case that is relatively uncommon in practice.

2. **Schema Design Preference**: Well-designed schemas typically use records (structs) with known fields rather than dynamic maps. Maps are often a code smell indicating missing domain modeling.

3. **Avro Compatibility**: While Avro supports maps, they can be represented as relaxed structs without full value validation. This is a pragmatic trade-off.

4. **Future Extension**: The decision can be revisited if real-world demand emerges.

## Decision

**We will NOT implement a dedicated `Map` combinator.**

For Avro schema import:
- Avro `map` types will be mapped to `Struct({})` (empty struct, non-strict mode)
- This accepts any object but relaxes value type validation
- A warning or annotation may be added to indicate reduced validation fidelity

Recommended practice:
- Prefer Avro `record` types over `map` types in schema design
- Use `Struct` with explicit field definitions where possible

## Consequences

### Positive

- Simpler library API with fewer combinators to learn
- Encourages better schema design practices (explicit fields over dynamic maps)
- Reduces maintenance burden

### Negative

- Avro maps lose value-type validation when converted to Janus validators
- Users who genuinely need dictionary validation must implement custom solutions
- Not 100% fidelity with Avro type system

### Neutral

- Decision can be revisited in the future if demand warrants
- Users can implement custom Map-like validation using `withGenerator` or custom validators if needed

## Alternatives Considered

1. **Implement full Map combinator**: Rejected due to complexity vs. utility trade-off
2. **Map to Quantifier of key-value pairs**: Awkward API, loses object semantics
3. **Ignore map types entirely**: Too restrictive, some representation is better than none

