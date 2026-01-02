# ADR-006: Move Generators from Core to Domain Package

## Status
Accepted

## Date
2026-01-02

## Context
- Generators currently live in `@janus-validator/core`, coupled to the legacy core `Domain` implementations.
- The new `@janus-validator/domain` package is the canonical domain model per ADR-002/004/005.
- Maintaining generators in core duplicates domain logic and blocks consumers that only need domain + generation without pulling in all of core.

## Decision
- Move all generator implementations from core into the domain package.
- Do not rewrite generator logic; relocate the existing code and refactor imports/types to use `@janus-validator/domain` classes.
- Expose generators from the domain package (e.g., `@janus-validator/domain/generators`), and update core to consume them from domain rather than hosting its own copies.

## Consequences
### Positive
- Single source of truth for domains and their generators.
- Core becomes slimmer and delegates to domain for generation.
- Consumers needing only domain + generation can depend solely on `@janus-validator/domain`.

### Negative
- Breaking change for core consumers importing generators from their old locations; requires migration guidance.
- Temporary churn in build/test wiring while paths change.

### Plan / Migration
- Physically move generator source files and tests from core to domain under a `generators` namespace.
- Update generator imports to reference `@janus-validator/domain` domain classes (no `core` Domain types).
- Re-export generators from the domain package; adjust core to import from domain.
- Update tsconfig/jest paths and package.json dependencies as needed.
- Provide a migration note: imports should switch from core paths to `@janus-validator/domain/generators`.
- Keep behavior and APIs identical; no functional rewrites.

