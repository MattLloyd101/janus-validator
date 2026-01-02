# ADR-004: Regex Parser Extraction and RegexDomain AST Mapping

## Status
Accepted

## Date
2026-01-02

## Context
- `RegexDomain` in `@janus-validator/domain` currently wraps the built-in `RegExp` for `contains` checks, which prevents composability with other domains and limits precise `encapsulates` reasoning.
- A Regex AST parser already exists in the core package; we want to reuse it and eventually make core depend on the shared implementation.
- We enforce a portable subset (no flags/backrefs/lookarounds/\\w/\\s/\\b) and fail fast on unsupported constructs.

## Decision
- Create a new package `@janus-validator/regex-parser` that exposes the Regex AST parser currently living in core.
- Refactor `RegexDomain` to parse patterns with `regex-parser`, traverse the AST, and map each node to existing domain types (e.g., concatenation → `Sequence`-like domain via `Struct`/`Quantifier`, alternation → `AlternationDomain`, literals/char classes → `FiniteDomain`/`ContiguousDomain` as appropriate).
- Keep the portable subset as the accepted language; any unsupported AST node or flag must throw with a clear error.
- Core will be updated later to consume `regex-parser`; for now only `@janus-validator/domain` depends on it.

## Consequences
### Positive
- Enables finer-grained `encapsulates` and set operations on regex-derived domains.
- Single source of truth for regex parsing, reusable by domain (now) and core (later).
- Maintains portability by enforcing the existing subset with explicit errors.

### Negative
- Additional package to maintain and publish.
- Mapping complexity increases; must ensure AST→Domain mapping stays exact-first.

### Follow-ups
- Migrate core to use `@janus-validator/regex-parser`.
- Expand tests to cover AST mapping, edge cases, and guardrails.
- Consider exposing a shared regex AST schema for tooling.

