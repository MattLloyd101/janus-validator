# ADR-003: Property-Based Testing for the Domain Package

## Status
Proposed

## Date
2026-01-02

## Context
- The Domain package is the semantic core for validation and generation; correctness here underpins schema compatibility and other packages (see ADR-002).
- Current tests are mostly example-based; they miss edge cases, algebraic laws, and regressions across relations and set operations.
- ADR-002 requires generator/validator alignment; property-based testing (PBT) is the practical enforcement mechanism.
- Two testing modes are needed: (1) exhaustive/complete runs for full coverage and archived verification, and (2) fast, time-bounded CI runs for signal without prohibitive cost.

## Decision
- Adopt property-based testing as the default strategy for Domain invariants, using `fast-check` with Jest/ts-jest.
- Provide two standardized profiles:
  - **Complete (out-of-band):** Exhaustive or combinatorial coverage per domain where feasible; intended for scheduled/manual runs. Archive seeds, run counts, and summarized outputs as verification artifacts.
  - **CI (time-bounded/randomized):** Time- or run-limited sampling across domains for fast feedback. Deterministic via logged seeds; reproducible by re-running with the same seed and run count.
- Configuration knobs (env-driven):
  - `JANUS_PBT_PROFILE` = `ci` (default in CI) or `complete` (manual/scheduled).
  - Overrides: `JANUS_PBT_SEED`, `JANUS_PBT_NUM_RUNS`, optional `JANUS_PBT_MAX_TIME_MS` for CI budget.
- Determinism and debuggability:
  - Always log the failing seed/counterexample; shrinking stays on.
  - Keep CI logs compact (no verbose per-case logging).
- Property scopes (minimum expectations):
  - **Soundness:** Values generated from a domain (or derived arbitrary) must satisfy `contains`.
  - **Algebraic laws:** Commutativity/associativity/idempotence for `union`/`intersect`; subtraction identities; normalization idempotence; encapsulation partial order (reflexive/transitive, antisymmetry where defined).
  - **Boundary/guardrails:** Regex portable-subset enforcement; `StructDomain` strict vs non-strict; `QuantifierDomain` length bounds; `CustomGeneratorDomain` treated as generation-only (excluded from schema semantics).
  - **Compatibility stance:** Prefer exact/“fail fast” over `unknown` for standard-library domains (per ADR-002).
- Test organization:
  - Place PBT suites under `packages/domain/tests/property/`.
  - Provide helpers: domain→arbitrary adapters, profile-aware `fc.assert` wrapper, and logging of seeds/run counts.
- Tooling:
  - Add `fast-check` as a dev dependency in the Domain package.
  - Optional jest setup hook to read profile env vars and expose seeded runs.

## Consequences
- **Positive:** Higher confidence in invariants; reproducible failures; aligns with ADR-002’s generator/validator contract; separates exhaustive verification from fast CI.
- **Negative:** Longer runtime for complete mode; added dependency and helper maintenance.
- **Mitigations:** Keep CI profile time-bounded; schedule complete runs out-of-band and archive their outputs.

## Alternatives Considered
- Generate core domains from Coq and transpile (Coq → OCaml → TypeScript):
  - Rejected: produced non-idiomatic TS, awkward interfaces, and would force Church-numeral-style integer handling; toolchain friction too high.
- Certificate generation in TS with Coq validator for certificates/outputs:
  - Rejected: technically viable but vastly increases implementation complexity with minimal practical gain.
- Dependent-type checking as a primary strategy:
  - Rejected: tooling/ecosystem cost is high; PBT offers a pragmatic balance of coverage, maintainability, and debuggability.
- Example-only testing:
  - Rejected: insufficient coverage of algebraic laws and edge cases.

