# @janus-validator/domain

Domain algebra for Janus: exact-first relations and set operations that mirror validator semantics. See ADR-002 for the design principles (exactness over approximation, tri-state `encapsulates`, fail-fast on unsupported constructs, and normalization for predictability).

## Supported domain shapes
- `FiniteDomain` — explicit value sets.
- `ContiguousDomain` / `BigIntDomain` — inclusive numeric ranges.
- `BytesDomain` — byte-array length bounds.
- `StringDomain` — string length bounds.
- `RegexDomain` — portable regex subset (no flags/backrefs/lookarounds/\\w/\\s/\\b).
- `StructDomain` — object fields with optional `strict` key control.
- `QuantifierDomain` — array-like repetition with `min`/`max`.
- `AlternationDomain` — normalized unions of other domains.

Regex parsing is delegated to `@janus-validator/regex-parser`, which enforces the portable subset and provides an AST for composability.

## Relations and set operations
- `Domains.relations.encapsulates(sup, sub)` → tri-state result with reasons for `false`/`unknown`.
- `Domains.set.union|intersect|subtract` → exact-first, normalized outputs; fail-fast on unsupported combos.
- Normalization flattens alternations and merges adjacent/overlapping ranges.

## Guardrails
- Regex is restricted to the portable subset; unsupported constructs throw on domain creation.
- Set operations return empty or throw rather than approximate when unsupported.

## Scripts (what and how)
- `npm -w @janus-validator/domain run build` — TypeScript compile to `dist/`.
- `npm -w @janus-validator/domain run watch` — Build in watch mode.
- `npm -w @janus-validator/domain run clean` — Remove `dist/`.
- `npm -w @janus-validator/domain test` — Run Jest test suite (ts-jest).
- `npm -w @janus-validator/domain run test:watch` — Jest in watch mode.
- `npm -w @janus-validator/domain run test:coverage` — Jest with coverage reports (enforces thresholds in `jest.config.js`).
- `npm -w @janus-validator/domain run coverage` — Jest coverage with text-summary reporter (fast local summary).
- `npm -w @janus-validator/domain run test:pbt:short` — Property-based tests with short profile (`JANUS_PBT_PROFILE=short`).
- `npm -w @janus-validator/domain run test:pbt:long` — Property-based tests with long profile (`JANUS_PBT_PROFILE=long`).

