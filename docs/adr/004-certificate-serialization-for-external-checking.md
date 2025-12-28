# ADR-004: Certificate Serialization for External Checking

## Status
Proposed

## Date
2025-12-28

## Context
- ADR-003 establishes certificates as the canonical AST for domains and a small trusted kernel. External proof/checking tools now need a stable, machine-readable representation of certificates (and witness identity) to validate correctness outside the runtime.
- Current certificates live as in-memory objects; without a stable serialized form, external checkers cannot consume them deterministically.

## Decision
- Add a `serialize(): SerializedDomainCert<T>` method to `DomainCert` and implement it on all concrete certificates (`FiniteCert`, `ContiguousCert`, `UnionCert`, `IntersectCert`, `ComplementCert`).
- Serialized shapes:
  - `finite`: `{ kind: "finite", id?, values }`
  - `contiguous`: `{ kind: "contiguous", id?, min, max, witness: { id } }`
  - `union`: `{ kind: "union", id?, left, right }`
  - `intersect`: `{ kind: "intersect", id?, left, right }`
  - `complement`: `{ kind: "complement", id?, of }`
- Witness identity is **formally defined and hardcoded**, not dynamically assigned. Each supported witness must declare a stable identifier (e.g., a well-known string or enum key) that is serialized verbatim so the same witness can be recognized across processes and runs.
- Output is JSON-friendly and suitable for `JSON.stringify` to hand off to external checkers.
- Tests will assert serialized shapes per certificate class to keep the existing 1:1 test-to-folder mapping.

## Consequences
- External tooling can consume serialized certificates without needing internal code.
- Formal, hardcoded witness IDs enable consistent handling of contiguous certificates grouped by witness identity across processes/runs; dynamic per-instance IDs are disallowed.
- Clear serialization contracts reduce drift between runtime behavior and external proofs; adding new cert kinds will require extending the serialized ADT and tests.

## References
- ADR-003: Certificate-Based Domain System with Trusted Kernel and ContiguousDomain

