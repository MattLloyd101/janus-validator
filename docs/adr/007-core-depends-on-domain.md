# ADR-007: Core Depends on Domain Package for Domains and Generators

## Status
Proposed

## Date
2026-01-02

## Context
- Core currently hosts its own domain model and generators.
- ADR-002/004/005 established `@janus-validator/domain` as the canonical domain model and regex integration.
- ADR-006 moved generators into the domain package. Keeping duplicate domains/generators in core causes drift, duplication, and maintenance risk.

## Decision
- Remove the legacy domain and generator implementations from the core package.
- Core will import and use domains and generators from `@janus-validator/domain`.
- Public APIs in core that surface domains/generators should re-export the domain package equivalents (or provide thin wrappers that delegate), not maintain separate implementations.
- Core build/tests will be updated to rely on the domain package for all domain and generator behavior.

## Consequences
### Positive
- Single source of truth for domains and generators.
- Eliminates duplicate logic and divergence between core and domain.
- Simplifies maintenance and improves consistency for compatibility and generation semantics.

### Negative
- Breaking change for consumers importing core’s legacy domain/generator paths; requires migration guidance.
- Core now has an explicit dependency on `@janus-validator/domain`.

### Migration Plan
- Delete/retire core’s domain and generator sources/tests; replace imports in core with `@janus-validator/domain` equivalents.
- Add `@janus-validator/domain` as a dependency of core; adjust tsconfig/jest path mappings.
- Re-export domain/generator entry points from core (optional) to ease migration, or publish a migration guide for import path changes.
- Run and update core tests to use domain package domains/generators; remove obsolete fixtures.

