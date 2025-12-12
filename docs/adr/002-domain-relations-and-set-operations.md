# ADR-002: Domain Relations and Set Operations for Schema Compatibility

## Status
Proposed

## Date
2025-12-12

## Context
Janus models validation and generation through `Domain<T>` objects (see `packages/core/src/com/techlloyd/janus/Domain.ts`). Domains are the common substrate for:

- **Validation** via validators that expose a `domain`
- **Generation** via `Generator.generate(domain)`

We want a principled way to reason about **schema evolution / backwards compatibility** by comparing domains directly.

Example:
- `a = Integer(0, 5)` and `b = Integer(0, 10)`
- Every value accepted by `a` is also accepted by `b`, so **`b` is a superset of `a`**.

If we can formalize this as a domain relation (e.g. `b.encapsulates(a)`), then many compatibility questions become precise and automatable.

At the same time, not all domains are equally tractable (e.g. regex inclusion, cross-field constraints, custom generators). We want to **err on the side of exactness**, and treat niche/outlier cases as **unknown** rather than silently approximating.

## Decision
Introduce the concept of **Domain Relations** and **Domain Set Operations** as part of the core design.

### Scope for this version: no cross-field constraints
To keep domain relations **decidable and exact** (or “fail fast” for unsupported constructs), we explicitly exclude **cross-field constraints** from this version of the system.

Concretely:
- `Capture` / `Ref` (and their associated domain types) should be **removed** from the library for this version.
- This avoids introducing domains whose meaning depends on runtime context/control-flow and would otherwise force `unknown` results (or unsound approximations) in `encapsulates` and set operations.

We may revisit cross-field constraints in a future version with a dedicated design that preserves correctness (e.g. whole-schema constraint solving with explicit scoping/ordering rules), captured in a separate ADR.

### 1) Encapsulation (Set Inclusion)
Define a primary relation:

- **`encapsulates(b, a)`**: returns whether the set of values described by `a` is a subset of the set described by `b`.
  - In set notation: \( a \subseteq b \)
  - In compatibility terms: if `newDomain.encapsulates(oldDomain) === true`, then the new schema is **backwards compatible** with respect to that portion of the schema.

Because some comparisons cannot be decided exactly (or cannot be decided efficiently), `encapsulates` is **tri-state**:

```ts
export type RelationResult =
  | { result: 'true' }
  | { result: 'false'; reason: string }
  | { result: 'unknown'; reason: string };
```

**Policy:**
- For **standard library** domains and operations, we want `unknown` to be **exceptional**. The standard library should prefer to **constrain what it supports** (or fail fast on unsupported constructs) so that relations and set operations are **exact** and do not routinely produce `unknown`.
- We still keep `unknown` as part of the contract because Janus is intentionally **extensible**: external packages can define new domain types and operations that the standard library cannot reason about safely.
- When faced with an unrecognized/extension domain, the correct behavior is to return `{ result: 'unknown', reason }` rather than guessing. This avoids unsound compatibility conclusions.

### 2) Set Operations on Domains
Define set operations that construct new domains:

- **`union(a, b)`**: values accepted by either domain ( \( a \cup b \) )
- **`intersect(a, b)`**: values accepted by both domains ( \( a \cap b \) )
- **`subtract(a, b)`**: values in `a` that are not in `b` ( \( a \setminus b \) )

These operations should be implemented with an **exact-first** approach:

1. **Exact simplifications** for tractable domain types (e.g. numeric ranges, finite sets, length bounds).
2. If an exact result cannot be computed safely, return an explicit **“unknown/opaque”** representation (or refuse the operation), rather than producing a lossy domain.

### 3) Normalization
Introduce a “normalization” step for domains produced by set operations:

- flatten nested unions
- merge adjacent/overlapping numeric ranges
- dedupe identical alternatives
- reduce identity operations (e.g. `union(a, a) = a`)

Normalization makes `encapsulates` and set operations predictable and stable.

### 4) Generator/Validator Alignment Is a Design Constraint
Domains are intended to be the single source of truth for both validation and generation. As a design constraint, we aim for:

- **Soundness**: values generated from a domain must validate against that same domain.
- **Completeness (goal)**: for domains where it is feasible, generation should be capable of producing any value that the domain considers valid (i.e. generation and validation sets align).

This is actively enforced via **property-based testing**: generated values should always validate (soundness), and we should add targeted tests to increase confidence in coverage for each `DomainType` (a practical proxy for completeness).

When this alignment cannot be guaranteed (e.g. niche/complex domains), compatibility reasoning should still be **exact-first** and may return `unknown` rather than relying on generator behavior.

## Consequences
### Benefits
- **Schema evolution checks become mechanizable**: `newDomain.encapsulates(oldDomain)` becomes a default compatibility test.
- Encourages **domain-first introspection tooling**: diffing, reporting, and CI checks.
- Enables future “domain algebra” features and simplifications.

### Tradeoffs / Non-goals
- Some relations are inherently complex; we intentionally return **unknown** for cases that are:
  - not decidable with our supported information
  - likely to be niche / surprising
  - expensive to compute in worst cases

### Known complex areas
These cases may require extra care. Our default posture remains **exact-first**:
- Prefer an exact, decidable rule.
- If we cannot provide a correct rule, return `unknown` (or fail fast where appropriate).

- **`DomainType.REGEX_DOMAIN` inclusion**
  - **Stance:** We explicitly support only a **decidable subset** of regex so that domain relations and set operations can be **correct**.
  - For this supported subset, `encapsulates` should be **decidable** (though potentially expensive) and should not need to return `unknown`.
  - Any unsupported construct should trigger **defensive programming**: fail fast with an explicit error message that the construct is not supported by Janus domains.
  - Examples of constructs that must be rejected (non-exhaustive):
    - **Backreferences** (`\1`, `\k<name>`)
    - **Lookarounds** (`(?=...)`, `(?!...)`, `(?<=...)`, `(?<!...)`)
    - Other engine-specific extensions/subroutines
  - **Over-the-wire portability constraint:** the supported regex subset must have consistent meaning across runtimes.
    - We do **not** support regex flags in exported schemas by default (including dotAll / `s`). Flags are a major source of cross-runtime ambiguity.
    - We do **not** support ambiguous character-class escapes such as `\w`, `\s`, or `\b` in exported schemas. Different engines disagree on their Unicode behavior and word-boundary rules.
    - Prefer explicit literals and explicit character classes/ranges (e.g. `[A-Za-z0-9_]`, `[0-9]`, `[ \t\r\n]`) so the language is unambiguous and portable.
    - Allowed constructs (portable subset):
      - literals and escapes for common control characters: `\n`, `\r`, `\t`, `\f`, `\v`, `\0` (and escaping metacharacters)
      - character classes with literals and ranges: `[abc]`, `[a-z]`, `[^...]`
      - concatenation, alternation `|`
      - grouping `(...)` and non-capturing `(?:...)` (capturing is ignored for semantics)
      - quantifiers: `*`, `+`, `?`, `{n}`, `{n,}`, `{n,m}`
      - anchors `^` and `$` (as position constraints)
    - Any pattern using unsupported flags or unsupported constructs must fail fast with an explicit error (e.g. “Unsupported regex construct: \\b (word boundary) is not portable”).
- **`CUSTOM_GENERATOR_DOMAIN`**
  - `CUSTOM_GENERATOR_DOMAIN` is an **internal generation override**, not a semantic validation domain.
  - It exists to improve developer ergonomics for fixture generation (e.g. realistic names from a curated list) **without restricting accepted user input**.
  - This is a deliberate exception to “validation and generation sets align”, and it should be treated as **code-only** (not something represented in external schemas).
  - **Schema export tooling must ignore/strip `CUSTOM_GENERATOR_DOMAIN` by default** (treating it as its `innerDomain`), so that over-the-wire schema compatibility is preserved.
    - If exporters choose to support it, it must be via an **explicit opt-in override** (e.g. “domain overrides” / “export generation hints”), not implicit behavior.
- **Compound string `_parts`-based constraints**
  - **Direction:** Treat all string constraints as a single *decidable* “string-language” model.
    - Compound strings (`_parts`) are concatenations of sub-languages (literals + other string domains), which remain regular/decidable under the supported subset.
    - Character-set strings (e.g. domains carrying an internal `_charSet`) are also regular/decidable.
  - As with regex, any unsupported string constraint representation should **fail fast** with explicit errors rather than returning `unknown`.
  - Note: for practicality and correctness, the string-language model should be **symbolic** (ranges/classes) rather than enumerating full Unicode alphabets.

## Implementation Notes (Guidance)
The implementation should likely take the form of a small relations/algebra module (e.g. `Domains.relations.encapsulates(a, b)` and `Domains.set.union/intersect/subtract`) rather than methods attached to every domain instance, because `Domain<T>` is a lightweight structural interface.

Recommended properties of the implementation:
- **Pure, deterministic** operations (no RNG)
- **Explainability**: return `reason` strings for `false`/`unknown`
- **Exact-first**: treat “unknown” as acceptable and expected in niche scenarios

## Follow-ups
- Decide public API shape (`Domains` namespace module vs methods).
- Add a normalization pass for `ALTERNATION_DOMAIN` and range-like domains.
- Define exact `encapsulates` rules for tractable domain types:
  - `FINITE_DOMAIN`, `CONTIGUOUS_DOMAIN`, `BIGINT_DOMAIN`, `BYTES_DOMAIN`, `STRING_DOMAIN` length-bounds
  - `STRUCT_DOMAIN` (including `strict` semantics)
  - `SEQUENCE_DOMAIN`, `QUANTIFIER_DOMAIN`, `CAPTURE_DOMAIN`
- Define policy for `REGEX_DOMAIN` (supported subset + defensive parsing/errors) and any supported regex flags.
- Define a unified “string-language” direction (AST/model) that covers:
  - regex subset
  - compound strings (`_parts`)
  - character-set string domains
  - unions/concatenations/quantifiers of the above
  This model is the intended foundation for exact `encapsulates` and set operations on string-like domains.


