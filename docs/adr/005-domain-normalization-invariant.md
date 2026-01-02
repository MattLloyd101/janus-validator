# ADR-005: Domain Normalization Invariant at Creation Time

## Status
Accepted

## Date
2026-01-02

## Context
- The current `Domain<T>` interface (ADR-002) exposes `normalize(): Domain<T>` publicly.
- In practice, standard-library domains are meant to be created in normalized form, and set operations rely on normalized operands for exact-first semantics.
- Keeping `normalize` public encourages defensive re-normalization at call sites (e.g., `RegexDomain` visitor), obscuring the invariant and increasing surface area.
- We want a clear, enforced rule: all standard domains are normalized when constructed; normalization is an internal concern, not part of the public API.

## Decision
- Remove `normalize()` entirely from the public `Domain<T>` interface.
- Enforce normalization by construction: every standard library domain must be created already normalized; helper utilities should return normalized instances without requiring callers to invoke normalization.
- Keep any normalization helpers internal/protected; consumers cannot and should not call `normalize`.
- Update domain construction and set/relations code to rely on the creation-time normalization invariant instead of re-normalizing defensively.

## Consequences
### Positive
- Simplifies the public API and clarifies expectations for consumers.
- Eliminates redundant normalization calls and related performance overhead.
- Strengthens correctness by making normalization a construction-time guarantee rather than a best-effort at usage sites.

### Negative
- Breaking change for any external implementers or callers that relied on calling `normalize()` directly.
- Requires refactoring existing code to remove defensive `normalize()` calls and ensure constructors/factories enforce normalization.

### Follow-ups
- Ensure constructors/factories return normalized instances and retain any normalization helpers as internal/protected.
- Adjust set operations and relations to assume normalized inputs, adding targeted validation where necessary.
- Update documentation and tests to reflect the creation-time normalization invariant.

